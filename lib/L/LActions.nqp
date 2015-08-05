use NQPHLL;

use Util;
use Util::QAST;


class LActions is HLL::Actions {

    my sub isVar($node) {
        nqp::istype($node, QAST::Var)
            || insist-isa($node, QAST::Node)
    }

    my sub isLambda($node) {
        isOp($node, 'list')
            && (nqp::elems($node.list) > 1) # expect at least tag str and code block
            && isSVal($node[0])
            && (nqp::substr($node[0].value, 0, 1) eq 'λ')
        ;
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
            nqp::die("cannot turn into QAST::Node: " ~ describe($v));
        }
    }


    my sub lexVar(str $name, *%adverbs) {
        # Note: we set :decl to null_s explicitly to prevent bogus ":decl()" in dump
        QAST::Var.new(:name($name), :decl(nqp::null_s), :scope<lexical>, |%adverbs);
    }

    my sub locVar(str $name, *%adverbs) {
        # Note: we set :decl to null_s explicitly to prevent bogus ":decl()" in dump
        QAST::Var.new(:name($name), :decl(nqp::null_s), :scope<local>,   |%adverbs);
    }

    my sub mkDeclV($var, *%adverbs) {
        insist-isa($var, QAST::Var);
        QAST::Var.new(:name($var.name), :scope($var.scope), :node($var.node), :decl<var>,   |%adverbs);
    }

    my sub mkDeclP($var, *%adverbs) {
        insist-isa($var, QAST::Var);
        QAST::Var.new(:name($var.name), :scope($var.scope), :node($var.node), :decl<param>,   |%adverbs);
    }

    my sub mkBind($var, $value) {
        insist-isa($var, QAST::Var);
        my $valNode := asNode($value);
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
        my $out := QAST::Op.new(:op<hash>);
        if nqp::islist($contents) {
            my $length := nqp::elems($contents);
            nqp::die("mkHash expects a list with an even nr elems - has " ~ $length)
                if nqp::mod_i($length, 2);
            for $contents {
                $out.push(asNode($_));
            }
        } elsif nqp::ishash($contents) {
            for $contents {
                my $key := nqp::iterkey_s($_);
                my $val := nqp::iterval($_);
                $out.push(asNode($key));
                $out.push(asNode($val));
            }
        } else {
            nqp::die("mkHash expects a list or a hash - got " ~ nqp::reprname($contents));
        }
        $out;
    }

    my sub mkCall($fn, *@args) {
        my $out := QAST::Op.new(:op<call>);
        if nqp::isstr($fn) {
            $out.name($fn);
        } else {
            nqp::die("mkCall expects a str or a QAST::Node as 1st arg")
                unless nqp::istype($fn, QAST::Node);
            if (isVar($fn) && $fn.scope eq 'lexical') {
                $out.name($fn.name);
            } else {
                $out.push($fn);
            }
        }
        for @args {
            $out.push(asNode($_));
        }
        $out;
    }

    my sub mkRCall(str $fnName, *@args) {
        mkCall($fnName, |@args);
    }

    my sub isForced($node) {
        insist-isa($node, QAST::Node);
        $node.has_ann('forced');
    }

    my sub isDelayed($node) {
        insist-isa($node, QAST::Node);
        $node.has_ann('delayed');
    }

    my sub mkDelaySimple($node) {
        if isVal($node) || isOp($node, 'null') || isDelayed($node) || isVar($node) {
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
        if isVal($node) || isOp($node, 'null') || isOp($node, 'null') || isVar($node) {
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
            $node := mkRCall('.delayMemo', mkDelaySimple($node));

            #$node := QAST::Stmts.new(
            #    mkRCall('.say', mkConcat("# calling .delayMemo on\n", $node.dump)),
            #    $node
            #);
            
            $node.annotate('delayed', 'memo');
            $node;
        }
    }

    my sub mkForce($node) {
        nqp::die("mkForce expects a QAST::Node") 
            unless nqp::istype($node, QAST::Node);
        if isDelayed($node) {
            $node[0];
        } elsif isForced($node) || isVal($node) || isOp($node, 'null') {
            $node;
        } else {    # TODO: maybe inline if $node is already a QAST::Var
            my $out := mkRCall('.force', $node);
            $out.annotate('force', $node);
            $out;
        } # TODO: if $node is a call, and we introduce annotations re delayed status of return values...
    }

    my sub mkHashLookup($hash, :$key!) {
        nqp::die("mkHashLookup expects a str or QAST::Node as key")
            unless istype($key, str, QAST::Node);
        QAST::Op.new(:op<atkey>, $hash, asNode($key));
    }

    my sub mkListLookup($list, :$index!) {
        nqp::die("mkListLookup expects an int or a QAST::Node as index")
            unless istype($index, int, QAST::Node);
        QAST::Op.new(:op<atpos>, $list, asNode($index));
    }

    my sub mkConcat(*@args) {
        nqp::die("mkConcat expects at least 1 arg")
            unless nqp::elems(@args) > 0;
        my @nodes := [];
        for @args {
            @nodes.push(asNode($_));
        }

        my @compressed := [];
        my $current := nqp::shift(@nodes);
        for @nodes {
            if isSVal($current) && isSVal($_) {
                $current.value($current.value ~ $_.value);
            } else {
                @compressed.push(mkForce($current));
                $current := $_;
            }
        }
        @compressed.push(mkForce($current));

        my $n := nqp::elems(@compressed);
        if $n > 1 {
            $current := nqp::shift(@compressed);
            for @compressed {
                $current := QAST::Op.new(:op<concat>, $current, $_)
            }
        }
        $current;
    }

    my sub mkDie(*@msgPieces) {
        QAST::Op.new(:op<die>, mkConcat('ERROR: ', |@msgPieces));
    }

    my sub mkLambda2code($subject) {
        mkRCall('.->#n', $subject, 'λ', 1);
    }

    my sub mkLambda2freevars($subject) {
        mkRCall('.ifTag', $subject, 'λ',
            QAST::Block.new(:arity(1),
                mkDeclP(lexVar('id')),
                mkRCall('.sublist', $subject, 2)
            ),
            QAST::Op.new(:op<null>)
        );
    }

    has @!lambdaInfo;

    my sub mkRuntime($/, $topBlock, @lambdaInfo) {
        my $block := QAST::Stmts.new();
        my sub mkRFn(str $name, $paramNames, $cb, *%lexicals) {
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
            my $stmts := $cb(|@vars);
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
            my %info := $_;
            my $result := mkList(%info<binder>.name, %info<from>, %info<length>);
            my $lambda := %info<lambda>;
            my @freeVars := nqp::clone($lambda.list);
            @freeVars.shift;  # remove tag
            @freeVars.shift;  # remove code
            my %fvn2dBI := %info<fvn2dBI>;  # "free var names 2 deBruijn indices"
            my @fvn2dBI := [];
            for @freeVars { # need them in exactly the order in which they appear in the lambda
                my $name := $_.name;
                my $deBruijnIdx := %fvn2dBI{$name};
                @fvn2dBI.push($name ~ '.' ~ $deBruijnIdx);
            }
            $result.push(asNode(nqp::join(' ', @fvn2dBI)));
            $lambdaInfo.push($result);
        }
        $block.push(
            mkBind(lexVar('.λinfo', :decl<static>), $lambdaInfo)
        );

        mkRFn('.ifTag', <subject tag then else>, :tagAndId(nqp::null), -> $subject, $tag, $then, $else, $tagAndId {
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
        
        mkRFn('.->#n', <subject tag index>, -> $subject, $tag, $index {
            mkRCall('.ifTag', $subject, $tag,
                QAST::Block.new(:arity(1),
                    lexVar('_', :decl<param>),
                    mkListLookup($subject, :index($index))
                ),
                QAST::Op.new(:op<null>)
            )
        });
        
        mkRFn('.sublist', <list from>, -> $list, $from {
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
        
        mkRFn('.strOut', <v indent>, -> $v, $indent {
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
            my $val     := lexVar('val');

            mkBind($v, mkForce($v)),
            QAST::Op.new(:op<if>,
                QAST::Op.new(:op<isstr>, $v),
                mkRCall('.strLit', $v),
                mkRCall('.ifTag', 
                    $v, 
                    'λ',
                    QAST::Block.new(:arity(1),
                        mkBind(mkDeclP($id),          mkForce($id)),
                        mkBind(mkDeclV($fvars),       mkRCall('.sublist', $v, 2)),
                        mkBind(mkDeclV($info),        mkListLookup(lexVar('.λinfo'), :index($id))),
                        mkBind(mkDeclV($fvn2dBI),
                            QAST::Op.new(:op<split>, asNode(' '), mkListLookup($info, :index(3)))
                            #mkListLookup($info, :index(3))
                        ),
                        mkBind(mkDeclV($from),        mkListLookup($info, :index(1))),
                        mkBind(mkDeclV($length),      mkListLookup($info, :index(2))),
                        mkBind(mkDeclV($src),
                            mkConcat(
                                QAST::Op.new(:op<substr>, lexVar('.src'), $from, $length),
                                '  # :tag(', mkRCall('.strLit', mkListLookup($v, :index(0))), ')',
                            )
                        ),
                        mkBind(mkDeclV($i), 0),
                        QAST::Op.new(:op<for>, $fvn2dBI, QAST::Block.new(:arity(1),
                            mkDeclP($pair),
                            mkBind($pair, QAST::Op.new(:op<split>, asNode('.'), $pair)),
                            mkBind(mkDeclV($name), mkListLookup($pair, :index(0))),
                            mkBind(mkDeclV($dBI), mkListLookup($pair, :index(1))),
                            mkBind(mkDeclV($val), mkListLookup($fvars, :index($i))),
                            mkBind($i, QAST::Op.new(:op<add_i>, $i, asNode(1))),
                            QAST::Op.new(:op<if>, 
                                QAST::Op.new(:op<not_i>, $dBI),
                                mkBind($dBI, '∞')           # show "∞" as deBruijn index of unbound var
                            ),
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
                                        mkRCall('.strOut', 
                                            $val,
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

        mkRFn('.delayMemo', <block>, :wasRun(0), :result(nqp::null), -> $block, $wasRun, $result {
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
        
        mkRFn('.force', <x>, -> $x {
            QAST::Op.new(:op<if>,
                QAST::Op.new(:op<isinvokable>, $x),
                mkCall($x),
                $x
            )
        });
        
        mkRFn('.say', <v>, -> $v {
            mkBind($v, mkForce($v)),
            QAST::Op.new(:op<say>,
                QAST::Op.new(:op<if>,
                    QAST::Op.new(:op<isstr>, $v),
                    $v,
                    mkRCall('.strOut', $v, '')
                )
            )
        });
        
        mkRFn('.strLit', <s>, -> $s {
            mkConcat('"', QAST::Op.new(:op<escape>, $s), '"');
        });
        
        mkRFn('.apply1', <f a1>, :result(nqp::null), -> $f, $a1, $result {
            mkBind($f, mkForce($f)),
            mkBind($result, mkCall(
                QAST::Op.new(:op<defor>,
                    mkLambda2code($f),
                    mkDie('cannot apply ', mkRCall('.strLit', $f), ' to ', mkRCall('.strOut', $a1, ''))
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
    
        mkRFn('.testDelay02', <delayed>, :simple(nqp::null), :memo(nqp::null), -> $delayed, $simple, $memo {
            mkBind($simple, mkDelaySimple($delayed)),
            mkBind($memo,   mkDelayMemo($delayed)),
            
            #$simple
            $memo
        });

        $topBlock.unshift($block);

        $topBlock;
    }

    my sub match2location($match) {
        my @lines := nqp::split("\n", nqp::substr($match.orig, 0, $match.from == 0 ?? $match.chars !! $match.from));
        my $lineN := nqp::elems(@lines);
        my $colN  := 1 + nqp::chars(@lines.pop);
        my $file := $*USER_FILE;
        hash(:file($file), :line($lineN), :column($colN), :match($match), :str("$file:$lineN:$colN"));
    }

    my sub panic($match, *@msg-pieces) {
        @msg-pieces.push("\n");
        @msg-pieces.push(loc2str(match2location($match)));
        nqp::die(join('', @msg-pieces));
    }

    my sub freeVars2locations(%fvs) {
        my @out := [];
        for %fvs {
            my $key := nqp::iterkey_s($_);
            my @vals := nqp::iterval($_);
            for @vals -> $val {
                die("not a Node: $key => ??")
                    unless nqp::istype($val, QUAST::Node);
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
        '   at ' ~ %l<str> ~ $varNameStr;
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
            nqp::die("stats expects a QAST::Node - got " ~ nqp::reprname($node))
                unless nqp::istype($node, QAST::Node);
            @results[0] := @results[0] + 1; # size of tree
            if nqp::istype($node, QAST::Block) {
                @results[1] := @results[1] + 1; # nr of Blocks
            } elsif isOp($node, 'list') {
                @results[2] := @results[2] + 1; # nr of Op(list)s
            } elsif isIVal($node) {
                @results[3] := @results[3] + 1; # nr of IVals
            } elsif isSVal($node) {
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
            panic($/, "Compile Error: no term found at all")
        );

        my $mainTerm := $mainTermMatch.ast;
        my $top-block := $*UNIT[0];

        my $fvs := $mainTerm.ann('FV') // [];
        my $fvs-count := nqp::elems($fvs);
        if $fvs-count > 0 {
            my $msg := 'Compile Error: unbound variable' ~ ($fvs-count > 1 ?? "s\n" !! "\n");
            for freeVars2locations($fvs) {
                $msg := $msg ~ loc2str($_) ~ "\n";
            }
            nqp::die($msg);
        }

        my $s := mkRuntime($/, $top-block, @!lambdaInfo);
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
            mkRCall('.say', mkConcat(
                ~nqp::elems(@!lambdaInfo), " lambdas\n",
                lexVar('.qastSize'), " QAST::Node s\n",
                lexVar('.blockCount'), " QAST::Block s\n",
                lexVar('.listCount'), " QAST::Op(list) s\n",
                lexVar('.ivalCount'), " QAST::IVal s\n",
                lexVar('.svalSize'), " chars ttl in ", lexVar('.svalCount'), " QAST::SVal s\n",
                "------------------------------------------------",
            )),
            #QAST::Op.new(:op<flushfh>, QAST::Op.new(:op<getstdout>)),
            
            #mkRCall('.say', mkConcat('.testDelay02 = ', mkRCall('.testDelay02', lexVar('.testDelay01')))),
            #mkRCall('.say', mkConcat('.testDelay02 = ', mkRCall('.testDelay02', lexVar('.testDelay01')))),
            
            mkBind($mainResult, mkRCall('.strOut', $mainTerm, '')),
            
            mkRCall('.say', "------------------------------------------------"),
            $mainResult,
        ));
        
        my $out := $*UNIT;
        $*UNIT.main(mkCall(QAST::BVal.new(:value($s))));
        #$*UNIT.load(...);

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

    method termlist2orMore($/) {
        my @terms := $/<term>;

        my $out := @terms.shift.ast;
        $out := mkApp($out, $_.ast)
            for @terms;
        $out.node($/);

        #reportFV('termlist2orMore', $/, $out.ann('FV'));
        make $out;
    }

    my sub mkApp($f, $a) {
        insist-isa($f, QAST::Node);
        insist-isa($a, QAST::Node);

        my $out := mkRCall('.apply1', $f, mkDelayMemo($a));
        
        copy-free-vars(:into($out), $f, $a);

        $f.annotate('parent', $out);
        $a.annotate('parent', $out);
        $out;
    }

    method term($/) {
        my $out := $/<t>.ast;
        #reportFV('term', $/, $out.ann('FV'));
        make $out;
    }

    method variable($/) {
        my str $name := ~$/;
        my $var := lexVar($name, :node($/));
        $var.annotate('FV', nqp::hash($name, [$var]));
        $var.annotate('deBruijnIdx', 0);    # 0 means "unbound"
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
        $out.annotate('FV', {});
        make $out;
    }

    my sub getBindingLambda($v) {
        nqp::die('getBindingLambda expects a QAST::Var - got ' ~ nqp::reprname($v))
            unless isVar($v);
        $v.has_ann('bound_at')
            ?? $v.ann('bound_at')
            !! nqp::null;
    }

    my sub copy-free-vars(:$into!, *@sources) {
        $into.annotate('FV', {})
            unless $into.has_ann('FV');
        my %target-FVs := $into.ann('FV');
        for @sources {
            my %src-FVs := $_.ann('FV');
            for %src-FVs {
                my $var-name    := $_.key;
                my @occurrences := $_.value;
                my @target-occurrences;
                if nqp::existskey(%target-FVs, $var-name) {
                    @target-occurrences := %target-FVs{$var-name};
                    @target-occurrences.push($_)
                        for @occurrences;
                } else {
                    %target-FVs{$_.key} := nqp::clone(@occurrences);
                }
            }
        }
        %target-FVs;
    }


    method definition($/) {
        panic($/, 'NYI');
    }

    method abstraction($/) {
        my $binder := mkDeclP(lexVar(~$/<varName>, :node($/<varName>)));
        my $body   := $/<body>.ast;

        if !$body.has_ann('FV') {
            nqp::die("missing annotation 'FV' in body\n" ~ $body.dump);
        }

        my $code := QAST::Block.new(:arity(1), :node($/), $binder, $body);
        
        my $infoIdx := nqp::elems(@!lambdaInfo);
        my $out := mkList(
            asNode('λ' ~ $infoIdx),
            $code
            # free vars will be added below
        );
        $body.annotate('parent', $out);
        $out.annotate('infoIdx', $infoIdx);

        my %info := hash(
            :lambda($out),
            :binder($binder),
            :from($/.from),
            :length(nqp::sub_i($/.to, $/.from)), # length; using nqp::sub_i in order to get an int
            :fvn2dBI(hash()), # free-var-names-to-deBruijn-indices will be inserted below
            :node($/),
        );
        @!lambdaInfo.push(%info);

        

        my %fvs := copy-free-vars(:into($out), $body);
        my @boundVars := nqp::defor(%fvs{$binder.name}, []);
        nqp::deletekey(%fvs, $binder.name);

        for @boundVars -> $bv {
            my int $i := 0;
            my $p := $bv;
            my @lambdaParents := [];
            while !($p =:= $out) {
                $p := $p.ann('parent');
                if isLambda($p) {
                    $i := $i + 1;
                    @lambdaParents.push($p);
                }
            }
            if nqp::elems(@lambdaParents) > 1 { # direct λ parent is *not us*, hence $bv free there
                @lambdaParents.pop();
                for @lambdaParents -> $lp {
                    my %info := @!lambdaInfo[$lp.ann('infoIdx')];
                    %info<fvn2dBI>{$bv.name} := $i;
                }

                # TODO: only in direct parent where it's free (if any)
                #my $directLambdaParent := @lambdaParents[0];
                #my %info := @!lambdaInfo[$lp.ann('infoIdx')];
                #%info<fvn2dBI>{$bv.name} := $i;
            }

            $bv.annotate('deBruijnIdx', $i);
            $bv.annotate('bound_at', $out);
            #if $binder.name eq 'zzz' {
            #    say($bv.name, ' with deBruijn index ', $i, ' bound at ', ~$/, ', direct λ-parent: ', $directLambdaParent[1].node);
            #}
        }
        
        my %fvn2dBI := %info<fvn2dBI>;  # "free var names 2 deBruijn indices"
        if nqp::elems(%fvs) > 0 {
            for %fvs {
                my $name := nqp::iterkey_s($_);
                my @vars := nqp::iterval($_);
                my $i := 0;
                for @vars -> $v {
                    my $j := 0;
                    my $duped := 0;
                    while !$duped && ($j < $i) {
                        my $w  := @vars[$j];
                        $duped := getBindingLambda($v) =:= getBindingLambda($w);
                        $j++;
                    }
                    if !$duped {
                        $out.push($v);
                        nqp::die($name ~ ' already maps to ' ~ %fvn2dBI{$name} ~ ' in ' ~ $/)
                            if nqp::existskey(%fvn2dBI, $name);
                        %fvn2dBI{$name} := 0;   # Note: we're coming bottom up, so the deBruijn index is not yet known
                                                #       it will be updated by the lambda that binds v
                    }
                    $i++;
                }
            }
        }
        
        make $out;
    }
}

sub MAIN(*@ARGS) {
    #say(isSVal(QAST::Block.new));
    #say(isSVal(QAST::SVal.new));
    #say(isSVal("asdf"));

    say(isOp(QAST::Block.new));
    say(isOp(QAST::Op.new(:op<bind>)));
    say(isOp(QAST::Op.new(:op<bind>), "null"));
    say(isOp(QAST::Op.new(:op<bind>), "bind"));
    say(isOp(QAST::Op.new(:op<bind>), 27));
    #say(isOp("aysdf"));

    say(lexVar('foo', :decl<param>).dump);
}
