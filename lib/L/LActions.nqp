use NQPHLL;


class LActions is HLL::Actions {

    my role Var {
        method declV() {
            my $out := nqp::clone(self);
            $out.decl('var');
            $out;
        }
        method declP() {
            my $out := nqp::clone(self);
            $out.decl('param');
            $out;
        }
    }

    my sub locVar(str $name, *%adverbs) {
        my $out := QAST::Var.new(
            :name($name),
            :scope<local>,
            |%adverbs
        );
        $out.HOW.mixin($out, Var);
        $out;
    }

    my sub lexVar(str $name, *%adverbs) {
        my $out := QAST::Var.new(
            :name($name),
            :scope<lexical>,
            |%adverbs
        );
        $out.HOW.mixin($out, Var);
        $out;
    }

    my sub asNode($v) {
        if nqp::isstr($v) {
            QAST::SVal.new(:value($v));
        } elsif nqp::isint($v) {
            QAST::IVal.new(:value($v));
        } elsif nqp::isnum($v) {
            QAST::NVal.new(:value($v));
        } elsif nqp::istype($v, QAST::Node) {
            $v;
        } else {
            nqp::die("cannot turn " ~ $v ~ " into a QAST::Node");
        }
    }

    my sub mkCall($fn, *@args) {
        my $out := QAST::Op.new(:op<call>);
        if nqp::isstr($fn) {
            $out.name($fn);
        } elsif nqp::istype($fn, QAST::Node) {
            if (nqp::istype($fn, QAST::Var) && $fn.scope eq 'lexical') {
                $out.name($fn.name);
            } else {
                $out.push($fn);
            }
        } else {
            nqp::die("mkCall expects a QAST::Node as 1st arg");
        }
        for @args {
            $out.push(asNode($_));
        }
        return $out;
    }

    my sub mkSCall(str $fnName, *@args) {
        mkCall($fnName, |@args);
    }

    my sub isVal($node) {
        if nqp::istype($node, QAST::Node) {
            nqp::istype($node, QAST::SVal) || nqp::istype($node, QAST::IVal) || nqp::istype($node, QAST::NVal)
            || nqp::istype($node, QAST::Op) && ($node.op eq 'null');
        } else {
            nqp::die("expected a QAST::Node");
        }
    }

    my sub isForced($node) {
        if nqp::istype($node, QAST::Node) {
            $node.has_ann('forced');
        } else {
            nqp::die("isForced expects a QAST::Node");
        }
    }

    my sub isDelayed($node) {
        if nqp::istype($node, QAST::Node) {
            $node.has_ann('delayed');
        } else {
            nqp::die("isDelayed expects a QAST::Node");
        }
    }

    my sub mkDelaySimple($node) {
        if !nqp::istype($node, QAST::Node) {
            nqp::die("mkDelaySimple expects a QAST::Node");
        }
        if isVal($node) || isDelayed($node) || nqp::istype($node, QAST::Var) {
            $node;
        } elsif isForced($node) {
            $node.ann('forced');
        } else {
            $node := QAST::Block.new(:arity(0), $node);
            $node.annotate('delayed', 'simple');
            $node;
        }
    }

    my sub mkDelayMemo($node) {
        if !nqp::istype($node, QAST::Node) {
            nqp::die("mkDelayMemo expects a QAST::Node");
        }
        if isVal($node) || nqp::istype($node, QAST::Var) {
            $node;
        } elsif isDelayed($node) {
            my $delayType := $node.ann('delayed');
            if $delayType eq 'memo' {
                $node;
            } elsif $delayType eq 'simple' {
                mkDelayMemo($node[0]);
            } else {
                nqp::die("mkDelayMemo: unknown delay type '$delayType' in\n" ~ $node.dump);
            }
        } elsif isForced($node) {
            mkDelayMemo($node.ann('forced'));
        } else {
            $node := mkSCall('.delayMemo', mkDelaySimple($node));

            #$node := QAST::Stmts.new(
            #    mkSCall('.say', mkConcat("# calling .delayMemo on\n", $node.dump)),
            #    $node
            #);
            
            $node.annotate('delayed', 'memo');
            $node;
        }
    }

    my sub mkForce($node) {
        if nqp::istype($node, QAST::Node) {
            if isDelayed($node) {
                $node[0];
            } elsif isForced($node) || isVal($node) {
                $node;
            } else {    # TODO: maybe inline if $node is already a QAST::Var
                my $out := mkSCall('.force', $node);
                $out.annotate('force', $node);
                $out;
            } # TODO: if $node is a call, and we introduce annotations re delayed status of return values...
        } else {
            nqp::die("mkForce expects a QAST::Node");
        }
    }

    my sub mkHashLookup($hash, :$key!) {
        if nqp::isstr($key) || nqp::istype($key, QAST::Node) {
            QAST::Op.new( :op<atkey>, $hash, asNode($key) );
        } else {
            nqp::die("need str or QAST::SVal as key");
        }
    }

    my sub mkListLookup($list, :$index!) {
        if nqp::isint($index) || nqp::istype($index, QAST::Node) {
            QAST::Op.new( :op<atpos>, $list, asNode($index) );
        } else {
            nqp::die("need int or QAST::IVal as index");
        }
    }

    my sub mkConcat(*@args) {
        if nqp::elems(@args) < 1 {
            nqp::die("need at least 1 arg for mkConcat");
        }
        my @nodes := [];
        for @args {
            nqp::push(@nodes, asNode($_));
        }

        my @compressed := [];
        my $current := nqp::shift(@nodes);
        for @nodes {
            if nqp::istype($current, QAST::SVal) && nqp::istype($_, QAST::SVal) {
                $current.value($current.value ~ $_.value);
            } else {
                nqp::push(@compressed, mkForce($current));
                $current := $_;
            }
        }
        nqp::push(@compressed, mkForce($current));

        if nqp::elems(@compressed) > 1 {
            $current := nqp::shift(@compressed);
            for @compressed {
                $current := QAST::Op.new(:op<concat>, $current, $_)
            }
        }

        return $current;
    }

    my sub mkDie(*@msgPieces) {
        QAST::Op.new(:op<die>, mkConcat('ERROR: ', |@msgPieces));
    }

    my sub mkLambda2freevars($subject) {
        mkSCall('.->#n', $subject, 'λ', 1);
    }

    my sub mkLambda2code($subject) {
        mkSCall('.->#n', $subject, 'λ', 2);
    }

    has @!lambdaInfo;

    my sub mkSetting($/, @lambdaInfo) {
        my $block := QAST::Block.new(:arity(0));

        my sub mkSFn(str $name, $paramNames, $callback, *%lexicals) {
            if nqp::isstr($paramNames) {
                $paramNames := [$paramNames];
            }
            my $body := QAST::Block.new(:name($name), :arity(nqp::elems($paramNames)));
            my @vars := [];
            for $paramNames {
                my $var := lexVar($_);
                $body.push($var.declP);
                @vars.push($var);
            }
            for %lexicals {
                my $var := lexVar(nqp::iterkey_s($_));
                my $val := nqp::iterval($_);
                my $decl := $var.declV;
                if !nqp::isnull($val) {
                    $decl := QAST::Op.new(:op<bind>, $decl, asNode($val))
                }
                $body.push($decl);
                @vars.push($var);
            }
            my $stmts := $callback(|@vars);
            if nqp::islist($stmts) {
                for $stmts { $body.push($_) }
            } else {
                $body.push($stmts);
            }
            $block.push(
                QAST::Op.new(:op<bind>, lexVar($name, :decl<static>), $body)
            );
        }

        $block.push(
            QAST::Op.new(:op<bind>, lexVar('.src', :decl<static>), asNode(~$/))
        );

        my $lambdaInfo := QAST::Op.new(:op<list>);
        for @lambdaInfo {
            my @info := $_;
            $lambdaInfo.push(QAST::Op.new(:op<list>, |@info));
        }
        $block.push(
            QAST::Op.new(:op<bind>, lexVar('.λinfo', :decl<static>), $lambdaInfo)
        );

        mkSFn('.ifTag', <subject tag then else>, -> $subject, $tag, $then, $else {
            my $tagAndId    := lexVar('tagAndId');
            
            $tagAndId.declV,
            QAST::Op.new(:op<if>,
                QAST::Op.new(:op<islist>, $subject),
                QAST::Stmts.new(
                    QAST::Op.new(:op<bind>, $tagAndId, mkListLookup($subject, :index(0))),
                    QAST::Op.new(:op<if>,
                        QAST::Op.new(:op<iseq_s>,
                            $tag,
                            QAST::Op.new(:op<substr>, $tagAndId, asNode(0), asNode(1)),
                        ),
                        mkCall($then, 
                            mkListLookup(:index(0), # extract id as int from str tagAndId
                                QAST::Op.new(:op<radix>,
                                    asNode(10),
                                    $tagAndId,
                                    asNode(1),
                                    asNode(0)
                                )
                            )
                        ),
                        mkForce($else)
                    ),
                ),
                mkForce($else)
            )
        });
        
        mkSFn('.->#n', <subject tag index>, -> $subject, $tag, $index {
            mkSCall('.ifTag', $subject, $tag,
                QAST::Block.new(:arity(1),
                    lexVar('_', :decl<param>),
                    mkListLookup($subject, :index($index))
                ),
                QAST::Op.new(:op<null>)
            )
        });
        
        mkSFn('.strOut', <v indent>, -> $v, $indent {
            my $id      := lexVar('id');
            my $info    := lexVar('info');
            my $src     := lexVar('src');
            my $from    := lexVar('from');
            my $length  := lexVar('length');
            my $fvars   := lexVar('fvars');
            my $fnames  := lexVar('fnames');
            my $i       := lexVar('i');
            my $name    := lexVar('name');
            my $var     := lexVar('var');

            QAST::Op.new(:op<bind>, $v, mkForce($v)),
            QAST::Op.new(:op<if>,
                QAST::Op.new(:op<isstr>, $v),
                mkSCall('.strLit', $v),
                mkSCall('.ifTag', 
                    $v, 
                    'λ',
                    QAST::Block.new(:arity(1),
                        QAST::Op.new(:op<bind>, $id.declP,          mkForce($id)),
                        QAST::Op.new(:op<bind>, $fvars.declV,       mkListLookup($v, :index(1))),
                        QAST::Op.new(:op<bind>, $info.declV,        mkListLookup(lexVar('.λinfo'), :index($id))),
                        QAST::Op.new(:op<bind>, $from.declV,        mkListLookup($info, :index(1))),
                        QAST::Op.new(:op<bind>, $length.declV,      mkListLookup($info, :index(2))),
                        QAST::Op.new(:op<bind>, $src.declV,
                            mkConcat(
                                QAST::Op.new(:op<substr>, lexVar('.src'), $from, $length),
                                '  # :tag(', mkSCall('.strLit', mkListLookup($v, :index(0))), ')',
                            )
                        ),
                        QAST::Op.new(:op<bind>, $fnames.declV,
                            QAST::Op.new(:op<split>,
                                asNode(' '),
                                mkListLookup($info, :index(3))
                            )
                        ),
                        QAST::Op.new(:op<bind>, $i.declV,           asNode(0)),
                        QAST::Op.new(:op<for>, $fnames, QAST::Block.new(:arity(1),
                            $name.declP,
                            QAST::Op.new(:op<bind>, $var.declV, mkListLookup($fvars, :index($i))),
                            QAST::Op.new(:op<bind>, $i, QAST::Op.new(:op<add_i>, $i, asNode(1))),
                            QAST::Op.new(:op<bind>, $src,
                                mkConcat($src, 
                                    "\n",
                                    $indent,
                                    '# where ',
                                    $name, 
                                    ' = ',
                                    QAST::Op.new(:op<if>,
                                        QAST::Op.new(:op<iseq_s>, $name, asNode('self')),
                                        asNode('...'),
                                        mkSCall('.strOut', 
                                            $var,
                                            mkConcat($indent, '#           ')
                                        ),
                                    )
                                )
                            )
                        )),
                        $src
                    ),
                    mkDelaySimple(QAST::Op.new(:op<reprname>, $v))
                )
            )
        });

        mkSFn('.delayMemo', <block>, :wasRun(0), :result(nqp::null), -> $block, $wasRun, $result {
            QAST::Block.new(:arity(0),
                QAST::Op.new(:op<if>, $wasRun,
                    $result,
                    QAST::Stmts.new(
                        QAST::Op.new(:op<bind>, $wasRun, asNode(1)),
                        QAST::Op.new(:op<bind>, $result, mkCall($block))
                    )
                )
            )
        });
        
        mkSFn('.force', <x>, -> $x {
            QAST::Op.new(:op<if>,
                QAST::Op.new(:op<isinvokable>, $x),
                mkCall($x),
                $x
            )
        });
        
        mkSFn('.say', <v>, -> $v {
            QAST::Op.new(:op<bind>, $v, mkForce($v)),
            QAST::Op.new(:op<say>,
                QAST::Op.new(:op<if>,
                    QAST::Op.new(:op<isstr>, $v),
                    $v,
                    mkSCall('.strOut', $v, '')
                )
            )
        });
        
        mkSFn('.strLit', <s>, -> $s {
            mkConcat('"', QAST::Op.new(:op<escape>, $s), '"');
        });
        
        mkSFn('.apply1', <f a1>, :result(nqp::null), -> $f, $a1, $result {
            QAST::Op.new(:op<bind>, $f, mkForce($f)),
            QAST::Op.new(:op<bind>, $result, mkCall(
                QAST::Op.new(:op<defor>,
                    mkLambda2code($f),
                    QAST::Op.new(:op<if>,
                        QAST::Op.new(:op<isinvokable>, $f),
                        $f,
                        mkDie('cannot apply ', mkSCall('.strLit', $f), ' to ', mkSCall('.strOut', $a1, ''))
                    )
                ),
                $a1
            )),
            mkForce($result),
        });
        
        $block.push(QAST::Op.new(:op<bind>, lexVar('.testDelay01', :decl<static>),
            mkDelayMemo(mkDelaySimple(
                QAST::Stmts.new(
                    QAST::Op.new(:op<say>, asNode('.testDelay01 forced!!!!')),
                    asNode('42')
                )
            ))
        ));
    
        mkSFn('.testDelay02', <delayed>, :simple(nqp::null), :memo(nqp::null), -> $delayed, $simple, $memo {
            QAST::Op.new(:op<bind>, $simple, mkDelaySimple($delayed)),
            QAST::Op.new(:op<bind>, $memo,   mkDelayMemo($delayed)),
            
            #$simple
            $memo
        });

        return $block;
    }

    my sub match2location($match) {
        my @lines := nqp::split("\n", nqp::substr($match.orig, 0, $match.from == 0 ?? $match.chars !! $match.from));
        my $lineN := nqp::elems(@lines);
        my $colN  := 1 + nqp::chars(@lines.pop);
        my $file := $*USER_FILES;
        hash(:file($file), :line($lineN), :column($colN), :match($match), :str("$file:$lineN:$colN"));
    }

    my sub freeVars2locations(%fvs) {
        my @out := [];
        for %fvs {
            my $key := nqp::iterkey_s($_);
            my @vals := nqp::iterval($_);
            for @vals -> $val {
                if !nqp::istype($val, QUAST::Node) {
                    die("not a Node: $key => ??");
                }
                my $loc := match2location($val.node);
                $loc{'name'} := $key;
                $loc{'var'}  := $val;
                @out.push($loc);
            }
        }
        @out;
    }

    my sub loc2str(%l) {
        my $varNameStr := nqp::existskey(%l, 'var')
            ?? '  (' ~ %l<var>.name ~ ')'
            !! ''
        ;
        return '   at ' ~ %l<str> ~ $varNameStr;
    }

    my sub reportFV(str $where, $match, %fvs) {
        say(nqp::elems(%fvs), " FVs in $where @ ", '"', nqp::escape($match), '"');
        my @locs := freeVars2locations(%fvs);
        for @locs {
            say(loc2str($_));
        }
    }

    my sub stats($node) {
        if !nqp::istype($node, QAST::Node) {
            nqp::die("stats expects a QAST::Node");
        }
        my sub _stats($node, @results) {
            @results[0] := @results[0] + 1; # size of tree
            if nqp::istype($node, QAST::SVal) {
                @results[1] := @results[1] + 1; # nr of SVals
                @results[2] := @results[2] + nqp::chars($node.value); # ttl size of SVals
            }
            for $node.list {
                _stats($_, @results);
            }
            @results;
        }
        _stats($node, [0, 0, 0]);
    }

    method TOP($/) {
        my $mainTermMatch := $/<termlist1orMore>;
        nqp::defor($mainTermMatch,
            nqp::die("Compile Error: no term found at all\n" ~ loc2str(match2location($/)) ~ "\n")
        );

        my $mainTerm := $mainTermMatch.ast;

        my $fvs := $mainTerm.ann('FV');
        if nqp::elems($fvs) > 0 {
            my $msg := "Compile Error: unbound variables\n";
            for freeVars2locations($fvs) {
                $msg := $msg ~ loc2str($_) ~ "\n";
            }
            nqp::die($msg);
        }

        my $s := mkSetting($/, @!lambdaInfo);
        my $quastSizeBinding := QAST::Op.new(:op<bind>, lexVar('.qastSize',  :decl<static>));   # will receive a value node later
        my $svalCountBinding := QAST::Op.new(:op<bind>, lexVar('.svalCount', :decl<static>));   # will receive a value node later
        my $svalSizeBinding  := QAST::Op.new(:op<bind>, lexVar('.svalSize',  :decl<static>));   # will receive a value node later
        $s.push($quastSizeBinding);
        $s.push($svalCountBinding);
        $s.push($svalSizeBinding);
        
        my $mainResult := locVar('mainResult');
        $s.push(QAST::Block.new(:blocktype<immediate>,
            $mainResult.declV,
            mkSCall('.say', mkConcat(
                ~nqp::elems(@!lambdaInfo), " lambdas\n",
                lexVar('.qastSize'), " QAST::Node s\n",
                lexVar('.svalSize'), " chars ttl in ", lexVar('.svalCount'), " QAST::SVal s\n",
                "------------------------------------------------",
            )),
            #QAST::Op.new(:op<flushfh>, QAST::Op.new(:op<getstdout>)),
            
            #mkSCall('.say', mkConcat('.testDelay02 = ', mkSCall('.testDelay02', lexVar('.testDelay01')))),
            #mkSCall('.say', mkConcat('.testDelay02 = ', mkSCall('.testDelay02', lexVar('.testDelay01')))),
            
            QAST::Op.new(:op<bind>, $mainResult, mkSCall('.strOut', $mainTerm, '')),
            
            mkSCall('.say', "------------------------------------------------"),
            $mainResult,
        ));
        
        my $out := QAST::CompUnit.new(
            :hll('L'),
            #:load(...),
            :main(mkCall(QAST::BVal.new(:value($s)))),
            $s
        );

        my @stats := stats($out);
        $quastSizeBinding.push(asNode(@stats[0] + 3));  # size (we're pushing 3 more right here)
        $svalCountBinding.push(asNode(@stats[1]));      # nr of SVal nodes
        $svalSizeBinding.push(asNode(@stats[2]));       # ttl nr of characters in SVal nodes

        make $out;
    }

    method termlist1orMore($/) {
        if nqp::elems($/<term>) == 1 {
            my $out := $/<term>[0].ast;
            #reportFV('termlist1orMore', $/, $out.ann('FV'));
            make $out;
        } else {
            self.termlist2orMore($/);
        }
    }

    my sub mkApp($f, $a) {
        my $out := mkSCall('.apply1', $f, mkDelayMemo($a));
        my $fv := nqp::clone($f.ann('FV'));
        for $a.ann('FV') {
            my $key := nqp::iterkey_s($_);
            my @vals := nqp::iterval($_);
            if nqp::existskey($fv, $key) {
                for @vals -> $val {
                    $fv{$key}.push($val);
                }
            } else {
                $fv{$key} := @vals;
            }
        }
        $out.annotate('FV', $fv);

        $out;
    }

    method termlist2orMore($/) {
        my $f := $/<term>.shift.ast;
        my $a := $/<term>.shift.ast;
        my $app := mkApp($f, $a);

        for $/<term> {
            $app := mkApp($app, $_.ast);
        }
        $app.node($/);
        #reportFV('termlist2orMore', $/, $app.ann('FV'));
        make $app;
    }

    method term($/) {
        my $out := $/<t>.ast;
        #reportFV('term', $/, $out.ann('FV'));
        make $out;
    }

    method variable($/) {
        my str $name := ~$/;
        my $var := lexVar($name, :node($/));
        my $fv := hash();
        $fv{$name} := [$var];
        $var.annotate('FV', $fv);
        make $var;
    }

    my %str-esc := hash(:b("\b"), :r("\r"), :n("\n"), :f("\f"), :t("\t"));
    nqp::bindkey(%str-esc, '"', '"');
    nqp::bindkey(%str-esc, '\\', '\\');

    method str-constant($/) {
#        say("###str-constant, 0: " ~ nqp::elems($/[0]));
        my $s := "";
        for $/[0] {
            if nqp::substr($_, 0, 1) eq '\\'  {
                my $esc := nqp::substr($_, 1, 1);
                if nqp::existskey(%str-esc, $esc) {
                    $s := $s ~ %str-esc{$esc};
                } else {
                    nqp::die("unknown escape sequence \\" ~ $esc);
                }
            } else {
                $s := $s ~ $_;
            }
        }
#        say("###str-constant: " ~ $s);
        my $out := asNode($s);
        $out.annotate('FV', hash());
        make $out;
    }

    method abstraction($/) {
        my $binder := lexVar(~$/<varName>, :node($/<varName>)).declP;
        my $body   := $/<body>.ast;

        my $code := QAST::Block.new(:arity(1), :node($/), $binder, $body);

        my %fvs := nqp::clone($body.ann('FV'));
        my @bound := nqp::defor(%fvs{$binder.name}, []);
        nqp::deletekey(%fvs, $binder.name);
        for @bound {
            $_.annotate('bound_by', $binder);
        }
        
        my @freeVarNames := [];
        my @freeVars := [];
        if nqp::elems(%fvs) > 0 {
            for %fvs {
                my $name := nqp::iterkey_s($_);
                my @vars := nqp::iterval($_);
                my $i := 0;
                for @vars -> $v {
                    my $j := 0;
                    my $duped := 0;
                    while !$duped && ($j < $i) {
                        my $b1 := $v.ann('bound_by');
                        my $b2 := @vars[$j].ann('bound_by');
                        $duped := (!nqp::istype($b1, QAST::Var) && !nqp::istype($b2, QAST::Var))     # both unbound
                                  || ((!nqp::istype($b1, QAST::Var) && !nqp::istype($b2, QAST::Var)) # OR both bound by...
                                      && ($b1.node =:= $b2.node)                                     # ...same thing in src
                                  )
                        ;
                        $j++;
                    }
                    if !$duped {
                        @freeVarNames.push($v.name);
                        @freeVars.push($v);
                    }
                    $i++;
                }
            }
        }

        my $id := nqp::elems(@!lambdaInfo);

        my @info := [
            asNode($binder.name),
            asNode($/.from),
            asNode(nqp::sub_i($/.to, $/.from)), # length
            asNode(nqp::join(' ', @freeVarNames)),
        ];
        my $lam := QAST::Op.new(:op<list>,
            asNode('λ' ~ $id),
            QAST::Op.new(:op<list>, |@freeVars),
            $code,
        );
        $lam.annotate('FV', %fvs);

        $lam.annotate('id', 'λ' ~ $id);
        @!lambdaInfo.push(@info);

        if !$body.has_ann('FV') {
            nqp::die("missing annotation 'FV' in body " ~ $/<body>);
        }
        
        make $lam;
    }
}

