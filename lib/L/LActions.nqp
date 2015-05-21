use NQPHLL;


class LActions is HLL::Actions {

    my sub locVar(str $name, *%adverbs) {
        QAST::Var.new(:name($name), :scope<local>,   |%adverbs);
    }

    my sub lexVar(str $name, *%adverbs) {
        QAST::Var.new(:name($name), :scope<lexical>, |%adverbs);
    }

    my sub mkDeclV($var, *%adverbs) {
        if !nqp::istype($var, QAST::Var) {
            nqp::die("mkDeclV expects a QAST::Var");
        }
        QAST::Var.new(:name($var.name), :scope($var.scope), :node($var.node), :decl<var>,   |%adverbs);
    }

    my sub mkDeclP($var, *%adverbs) {
        if !nqp::istype($var, QAST::Var) {
            nqp::die("mkDeclP expects a QAST::Var");
        }
        QAST::Var.new(:name($var.name), :scope($var.scope), :node($var.node), :decl<param>,   |%adverbs);
    }

    my sub mkBind($var, $value) {
        if !nqp::istype($var, QAST::Var) {
            nqp::die("mkBind expects a QAST::Var as 1st arg - got " ~ nqp::reprname($var));
        }
        my $valNode := asNode($value);
        if !nqp::istype($valNode, QAST::Node) {
            nqp::die("mkBind cannot grok 2nd arg - got " ~ nqp::reprname($value));
        }
        QAST::Op.new(:op<bind>, $var, $valNode);
    }

    my sub mkList(*@contents) {
        my @contentNodes := [];
        for @contents {
            @contentNodes.push(asNode($_));
        }
        QAST::Op.new(:op<list>, |@contentNodes);
    }

    my sub mkHash($contents) {
        if !nqp::islist($contents) {
            nqp::die("mkHash expects a list - got " ~ nqp::reprname($contents));
        }
        my $length := nqp::elems($contents);
        if nqp::mod_i($length, 2) {
            nqp::die("mkHash expects a list with an even nr elems - has " ~ $length);
        }
        my $out := QAST::Op.new(:op<hash>);
        for $contents {
            $out.push(asNode($_));
        }
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
            nqp::die("cannot turn into QAST::Node: " ~ nqp::reprname($v));
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

    my sub mkLambda2code($subject) {
        mkSCall('.->#n', $subject, 'λ', 1);
    }

    my sub mkLambda2freevars($subject) {
        mkSCall('.ifTag', $subject, 'λ',
            QAST::Block.new(:arity(1),
                mkDeclP(lexVar('id')),
                mkSCall('.sublist', $subject, 2)
            ),
            QAST::Op.new(:op<null>)
        );
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
                $body.push(mkDeclP($var));
                @vars.push($var);
            }
            for %lexicals {
                my $var := lexVar(nqp::iterkey_s($_));
                my $val := nqp::iterval($_);
                my $decl := mkDeclV($var);
                if !nqp::isnull($val) {
                    $decl := mkBind($decl, $val);
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
                mkBind(lexVar($name, :decl<static>), $body)
            );
        }

        $block.push(
            mkBind(lexVar('.src', :decl<static>), ~$/)
        );

        my $lambdaInfo := mkList();
        for @lambdaInfo {
            my @info := $_;
            $lambdaInfo.push(mkList(|@info));
        }
        $block.push(
            mkBind(lexVar('.λinfo', :decl<static>), $lambdaInfo)
        );

        mkSFn('.ifTag', <subject tag then else>, :tagAndId(nqp::null), -> $subject, $tag, $then, $else, $tagAndId {
            QAST::Op.new(:op<if>,
                QAST::Op.new(:op<islist>, $subject),
                QAST::Stmts.new(
                    mkBind($tagAndId, mkListLookup($subject, :index(0))),
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
        
        mkSFn('.sublist', <list from>, -> $list, $from {
            my $to    := lexVar('to');
            my $out   := lexVar('out');
            my $count := lexVar('count');
            my $n     := lexVar('n');
            
            mkDeclP($count, :default(QAST::Op.new(:op<elems>, $list))),
            mkBind(mkDeclV($n),   QAST::Op.new(:op<elems>, $list)),
            mkBind(mkDeclV($out), mkList()),
            mkBind(mkDeclV($to),  QAST::Op.new(:op<add_i>, $from, $count)),
            QAST::Op.new(:op<if>,
                QAST::Op.new(:op<isgt_i>, $to, $n),
                mkBind($to, $n)
            ),
            QAST::Op.new(:op<while>,
                QAST::Op.new(:op<islt_i>, $from, $to),
                QAST::Stmts.new(
                    QAST::Op.new(:op<push>, $out, mkListLookup($list, :index($from))),
                    mkBind($from, QAST::Op.new(:op<add_i>, $from, asNode(1))),
                )
            ),
            $out,
        });
        
        mkSFn('.strOut', <v indent>, -> $v, $indent {
            my $id      := lexVar('id');
            my $info    := lexVar('info');
            my $src     := lexVar('src');
            my $from    := lexVar('from');
            my $length  := lexVar('length');
            my $fvars   := lexVar('fvars');
            my $fvn2dBI := lexVar('fvn2dBI');  # "free var name 2 deBruijn index"
            my $i       := lexVar('i');
            my $pair    := lexVar('pair');
            my $name    := lexVar('name');
            my $dBI     := lexVar('dBI');   # "deBruijn index"
            my $var     := lexVar('var');

            mkBind($v, mkForce($v)),
            QAST::Op.new(:op<if>,
                QAST::Op.new(:op<isstr>, $v),
                mkSCall('.strLit', $v),
                mkSCall('.ifTag', 
                    $v, 
                    'λ',
                    QAST::Block.new(:arity(1),
                        mkBind(mkDeclP($id),          mkForce($id)),
                        mkBind(mkDeclV($fvars),       mkSCall('.sublist', $v, 2)),
                        mkBind(mkDeclV($info),        mkListLookup(lexVar('.λinfo'), :index($id))),
                        mkBind(mkDeclV($fvn2dBI),
                            #QAST::Op.new(:op<split>, asNode(' '), mkListLookup($info, :index(3)))
                            mkListLookup($info, :index(3))
                        ),
                        mkBind(mkDeclV($from),        mkListLookup($info, :index(1))),
                        mkBind(mkDeclV($length),      mkListLookup($info, :index(2))),
                        mkBind(mkDeclV($src),
                            mkConcat(
                                QAST::Op.new(:op<substr>, lexVar('.src'), $from, $length),
                                '  # :tag(', mkSCall('.strLit', mkListLookup($v, :index(0))), ')',
                            )
                        ),
                        mkBind(mkDeclV($i), 0),
                        QAST::Op.new(:op<for>, $fvn2dBI, QAST::Block.new(:arity(1),
                            mkDeclP($pair),
                            mkBind(mkDeclV($name), QAST::Op.new(:op<iterkey_s>, $pair)),
                            mkBind(mkDeclV($dBI), QAST::Op.new(:op<iterval>, $pair)),           # TODO: print "∞" for deBruijn index of unbound var
                            mkBind(mkDeclV($var), mkListLookup($fvars, :index($i))),
                            mkBind($i, QAST::Op.new(:op<add_i>, $i, asNode(1))),
                            mkBind($src,
                                mkConcat($src, 
                                    "\n",
                                    $indent,
                                    '# where ',
                                    $name,
                                    '(', $dBI, ')',
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
                        mkBind($wasRun, 1),
                        mkBind($result, mkCall($block))
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
            mkBind($v, mkForce($v)),
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
            mkBind($f, mkForce($f)),
            mkBind($result, mkCall(
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
        
        $block.push(mkBind(lexVar('.testDelay01', :decl<static>),
            mkDelayMemo(mkDelaySimple(
                QAST::Stmts.new(
                    QAST::Op.new(:op<say>, asNode('.testDelay01 forced!!!!')),
                    asNode('42')
                )
            ))
        ));
    
        mkSFn('.testDelay02', <delayed>, :simple(nqp::null), :memo(nqp::null), -> $delayed, $simple, $memo {
            mkBind($simple, mkDelaySimple($delayed)),
            mkBind($memo,   mkDelayMemo($delayed)),
            
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
        my sub _stats($node, @results) {
            if !nqp::istype($node, QAST::Node) {
                nqp::die("stats expects a QAST::Node - got " ~ nqp::reprname($node));
            }
            @results[0] := @results[0] + 1; # size of tree
            if nqp::istype($node, QAST::Block) {
                @results[1] := @results[1] + 1; # nr of Blocks
            } elsif nqp::istype($node, QAST::Op) {
                if $node.op eq 'list' {
                    @results[2] := @results[2] + 1; # nr of Op(list)s
                }
            } elsif nqp::istype($node, QAST::IVal) {
                @results[3] := @results[3] + 1; # nr of IVals
            } elsif nqp::istype($node, QAST::SVal) {
                @results[4] := @results[4] + 1; # nr of SVals
                @results[5] := @results[5] + nqp::chars($node.value); # ttl size of SVals
            }
            for $node.list {
                _stats($_, @results);
            }
            @results;
        }
        _stats($node, [0, 0, 0, 0, 0, 0]);
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
        # Note: cannot use mkBind here since this enforces an init value
        my $quastSizeBinding  := QAST::Op.new(:op<bind>, lexVar('.qastSize',   :decl<static>));   # will receive a value node later
        my $blockCountBinding := QAST::Op.new(:op<bind>, lexVar('.blockCount', :decl<static>));   # will receive a value node later
        my $listCountBinding  := QAST::Op.new(:op<bind>, lexVar('.listCount',  :decl<static>));   # will receive a value node later
        my $ivalCountBinding  := QAST::Op.new(:op<bind>, lexVar('.ivalCount',  :decl<static>));   # will receive a value node later
        my $svalCountBinding  := QAST::Op.new(:op<bind>, lexVar('.svalCount',  :decl<static>));   # will receive a value node later
        my $svalSizeBinding   := QAST::Op.new(:op<bind>, lexVar('.svalSize',   :decl<static>));   # will receive a value node later
        $s.push($quastSizeBinding);
        $s.push($blockCountBinding);
        $s.push($listCountBinding);
        $s.push($ivalCountBinding);
        $s.push($svalCountBinding);
        $s.push($svalSizeBinding);
        
        my $mainResult := locVar('mainResult');
        $s.push(QAST::Block.new(:blocktype<immediate>,
            mkDeclV($mainResult),
            mkSCall('.say', mkConcat(
                ~nqp::elems(@!lambdaInfo), " lambdas\n",
                lexVar('.qastSize'), " QAST::Node s\n",
                lexVar('.blockCount'), " QAST::Block s\n",
                lexVar('.listCount'), " QAST::Op(list) s\n",
                lexVar('.ivalCount'), " QAST::IVal s\n",
                lexVar('.svalSize'), " chars ttl in ", lexVar('.svalCount'), " QAST::SVal s\n",
                "------------------------------------------------",
            )),
            #QAST::Op.new(:op<flushfh>, QAST::Op.new(:op<getstdout>)),
            
            #mkSCall('.say', mkConcat('.testDelay02 = ', mkSCall('.testDelay02', lexVar('.testDelay01')))),
            #mkSCall('.say', mkConcat('.testDelay02 = ', mkSCall('.testDelay02', lexVar('.testDelay01')))),
            
            mkBind($mainResult, mkSCall('.strOut', $mainTerm, '')),
            
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
        $quastSizeBinding.push(asNode(@stats[0] + nqp::elems(@stats)));  # size (we're pushing more right here)
        $blockCountBinding.push(asNode(@stats[1]));     # nr of Block nodes
        $listCountBinding.push(asNode(@stats[2]));      # nr of IVal nodes
        $ivalCountBinding.push(asNode(@stats[3]));      # nr of IVal nodes
        $svalCountBinding.push(asNode(@stats[4]));      # nr of SVal nodes
        $svalSizeBinding.push(asNode(@stats[5]));       # ttl nr of characters in SVal nodes

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
        $f.annotate('parent', $out);
        $a.annotate('parent', $out);
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
        $var.annotate('deBruijnIdx', 0);
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
        my $binder := mkDeclP(lexVar(~$/<varName>, :node($/<varName>)));
        my $body   := $/<body>.ast;

        if !$body.has_ann('FV') {
            nqp::die("missing annotation 'FV' in body\n" ~ $body.dump);
        }

        my $code := QAST::Block.new(:arity(1), :node($/), $binder, $body);
        
        my $id := nqp::elems(@!lambdaInfo);
        my $out := mkList(
            asNode('λ' ~ $id),
            $code
            # free vars added below
        );
        $out.annotate('id', 'λ' ~ $id);
        $body.annotate('parent', $out);

        my %fvs := nqp::clone($body.ann('FV'));
        my @boundVars := nqp::defor(%fvs{$binder.name}, []);
        nqp::deletekey(%fvs, $binder.name);
        for @boundVars {
            $_.annotate('bound_by', $binder);
            #$_.annotate('deBruijnIdx', ???);
        }
        
        my @freeVarNames := [];
        my @fvn2dBI := [];  # "free var names 2 deBruijn indices"
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
                        $out.push($v);
                        @fvn2dBI.push($v.name);
                        @fvn2dBI.push($v.ann('deBruijnIdx'));
                    }
                    $i++;
                }
            }
        }

        my @info := [
            asNode($binder.name),
            asNode($/.from),
            asNode(nqp::sub_i($/.to, $/.from)), # length
            mkHash(@fvn2dBI),
        ];
        $out.annotate('FV', %fvs);

        @!lambdaInfo.push(@info);
        
        make $out;
    }
}

