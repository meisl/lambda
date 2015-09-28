use NQPHLL;

use Util;
use Util::QAST;
use Util::Compiler;
use Type;


my class NO_VALUE {}



my sub isLambda($node) {
    isOp($node, 'list')
        && (nqp::elems($node.list) > 1) # expect at least tag str and code block
        && isSVal($node[0])
        && (nqp::substr($node[0].value, 0, 1) eq 'λ')
    ;
}

my sub isApp($node) {
    isOp($node, 'call')
        && ($node.name eq '&apply1')
}

my sub isRCall($node) {
    isOp($node, 'call')
        && (nqp::index($node.name, '&') == 0)
}


my sub asNode($v) {
    if nqp::isstr($v) {
        QAST::SVal.new(:value($v));
    } elsif nqp::isint($v) {
        QAST::IVal.new(:value($v));
    } elsif nqp::isnum($v) {
        QAST::NVal.new(:value($v));
    } elsif nqp::islist($v) {
        mkList(|$v);
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

my sub mkDeclV($var, *%options) {
    insist-isa($var, QAST::Var);
    %options<decl> := 'var';
    nqp::clone($var).set(%options);
}

my sub mkDeclP($var, *%options) {
    insist-isa($var, QAST::Var);
    %options<decl> := 'param';
    nqp::clone($var).set(%options);
}

my sub mkBind($var, $value) {
    insist-isa($var, QAST::Var);
    $var := cloneAndSubst($var);
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

my sub isForced($node) {
    insist-isa($node, QAST::Node);
    $node.has_ann('forced');
}

my sub isDelayed($node) {
    insist-isa($node, QAST::Node);
    $node.has_ann('delayed');
}

my sub mkDelaySimple($node, *%options) {
    if isVal($node) || isOp($node, 'null') || isDelayed($node) || isVar($node) {
        $node;
    } elsif isForced($node) {
        $node.ann('forced');
    } else {
        $node := QAST::Block.new(:arity(0), $node);
        $node.annotate('delayed', 'simple');
        $node;
    }
    $node.set(%options);
    $node;
}

my sub mkCall($fn, *@args, *%options) {
    my $out := QAST::Op.new(:op<call>, |%options);
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

my $runtime;
my %runtime-fns-types := {};

my sub mkRCall(str $fnName, *@args, *%options) {
    nqp::die("invalid runtime fn name $fnName")
        unless nqp::index($fnName, '&') == 0;
    #nqp::die("no such runtime fn: $fnName")
    #    unless nqp::existskey(%runtime-fns-types, $fnName);
    mkCall($fnName, |@args, |%options);
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
        #my $wasRun := lexVar('wasRun');
        #my $result := lexVar('result');
        #my $out := QAST::Block.new(:blocktype<immediate>),
        #    mkBind(mkDeclV($wasRun), 0),
        #    mkDeclV($result),
        #    QAST::Block.new(:arity(0),
        #        QAST::Op.new(:op<if>,
        #            nqp::clone($wasRun),
        #            nqp::clone($result),
        #            QAST::Stmts.new(
        #                mkBind($wasRun, 1),
        #                mkBind($result, $node)
        #            )
        #        )
        #    )
        #);

        my $out := mkRCall('&delayMemo', mkDelaySimple($node));
        $out.node($node.node);

        ##$node := QAST::Stmts.new(
        ##    mkRCall('&say', mkConcat("# calling .delayMemo on\n", $node.dump)),
        ##    $node
        ##);
        
        $out.annotate('delayed', 'memo');
        $out;
    }
}

my sub mkForce($node) {
    insist-isa($node, QAST::Node);
    if isDelayed($node) {
        $node[0];
    } elsif isForced($node) || isVal($node) || isOp($node, 'null') {
        $node;
    } else {    # TODO: maybe inline if $node is already a QAST::Var
        my $out := mkRCall('&force', $node);
        $out.annotate('forced', $node);
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
            if $current.returns =:= str || isOp($current, 'concat') || isOp($current, 'escape') {
                @compressed.push($current);
            } else {
                @compressed.push(mkForce($current));
            }
            $current := $_;
        }
    }
    if $current.returns =:= str || isOp($current, 'concat') || isOp($current, 'escape') {
        @compressed.push($current);
    } else {
        @compressed.push(mkForce($current));
    }

    my $n := nqp::elems(@compressed);
    if $n > 1 {
        $current := nqp::shift(@compressed);
        for @compressed {
            $current := QAST::Op.new(:op<concat>, :returns(str), $current, $_)
        }
    } else {
        $current.returns(str);
    }
    $current;
}

my sub mkDie(*@msgPieces) {
    QAST::Op.new(:op<die>, mkConcat('ERROR: ', |@msgPieces));
}

my sub mkLambda2code($subject) {
    mkRCall('&->#n', $subject, 'λ', 1);
}

my sub mkLambda2freevars($subject) {
    mkRCall('&ifTag', $subject, 'λ',
        QAST::Block.new(:arity(1),
            mkDeclP(lexVar('id')),
            mkRCall('&sublist', $subject, 2)
        ),
        QAST::Op.new(:op<null>)
    );
}

my sub mkTypecase($subject, *%clauses) {
    insist-isa($subject, QAST::Node);
    my $out := QAST::Op.new(:op<typecase>, :name($subject.name));
    for %clauses {
        my $k := $_.key;
        my $v := $_.value;
        insist-isa($v, QAST::Node, :desc("typecase clause '$k'"));
        $v.named($k);
        $out.push($v);
    }
    $out;
}



my sub make-runtime() {
    my $block := QAST::Stmts.new();
    my sub mkRFn(str $name, $paramNames, $cb, :$returns = NO_VALUE, *%lexicals) {
        nqp::die("invalid runtime fn name $name")
            unless nqp::index($name, '&') == 0;
        
        if nqp::isstr($paramNames) {
            $paramNames := [$paramNames];
        }

        #my @paramTypes := [];
        #if $returns =:= NO_VALUE {
        #    nqp::die("need a type (:returns) for runtime fn $name");
        #} else {
        #    my $temp := $returns;
        #    for $paramNames {
        #        nqp::die("invalid type for fn $name: " ~ typeToStr($returns))
        #            unless nqp::isconcrete($temp) && nqp::istype($temp, FnType);
        #        @paramTypes.push($temp.in);
        #        $temp := $temp.out;
        #    }
        #}
        
        my $body := QAST::Block.new(:name($name), :arity(nqp::elems($paramNames)));
        my @vars  := [];
        my %named := {};
        @vars.push(lexVar($_))
            for $paramNames;
        %named{$_.key} := lexVar($_.key)
            for %lexicals;
        
        my $stmts := $cb(|@vars, |%named);
        
        # make declarations *AFTER* the call to $cb, ie. from the actual vars passed to $cb!
        for @vars {
            $body.push(mkDeclP($_));
        }
        for %named {
            my $var  := $_.value;
            my $decl := mkDeclV($var);
            my $initial-value := %lexicals{$var.name};
            unless nqp::existskey(%lexicals, $var.name) && !($initial-value =:= NQPMu) {
                nqp::die("mkRFn('$name'): invalid entry for lexical " ~ $var.name ~ ': ' ~ describe($initial-value));
            }
            $body.push($initial-value =:= NO_VALUE
                ?? $decl
                !! mkBind($decl, $initial-value)
            );
        }
        my $tBody;
        if nqp::islist($stmts) {
            for $stmts {
                $body.push($_);
            }
        } else {
            $body.push($stmts);
        }
        my $binding := mkBind(lexVar($name, :decl<static>), $body);
        $block.push($binding);

        $binding;
    }

    mkRFn('&banner', [], 
        #:returns(Type.Fn(Type.Void, Type.Str)),
    -> {
        asNode("This is L v0.0.1"),
    });

    mkRFn('&strLit', <s>, 
        #:returns(Type.Fn(Type.Str, Type.Str)), 
        :foo<bar>,  # prevent it from being inlined
    -> $s {
        #mkConcat('"', QAST::Op.new(:op<escape>, $s), '"'); # mkConcat inserts mkForce, which ain't working on Op escape
        QAST::Op.new(:op<concat>,
            asNode('"'),
            QAST::Op.new(:op<concat>,
                QAST::Op.new(:op<escape>, $s),
                asNode('"')
            )
        );
    });
    
    mkRFn('&sublist', <list from>, 
        #:returns(Type.Fn(NQPArray, Type.Int, NQPArray)), 
        :out([]),
    -> $list, $from, :$out! {
        my $to    := lexVar('to');
        my $count := lexVar('count');
        my $n     := lexVar('n');
        
        mkBind(mkDeclV($n),     QAST::Op.new(:op<elems>, $list)),
        mkBind(mkDeclV($count), cloneAndSubst($n)),
        mkBind(mkDeclV($to),    QAST::Op.new(:op<add_i>, $from, cloneAndSubst($count))),
        QAST::Op.new(:op<if>,
            QAST::Op.new(:op<isgt_i>, cloneAndSubst($to), cloneAndSubst($n)),
            mkBind(cloneAndSubst($to), cloneAndSubst($n))
        ),
        QAST::Op.new(:op<while>,
            QAST::Op.new(:op<islt_i>, cloneAndSubst($from), cloneAndSubst($to)),
            QAST::Stmts.new(
                QAST::Op.new(:op<push>, cloneAndSubst($out), mkListLookup(cloneAndSubst($list), :index(cloneAndSubst($from)))),
                mkBind(cloneAndSubst($from), QAST::Op.new(:op<add_i>, cloneAndSubst($from), asNode(1))),
            )
        ),
        cloneAndSubst($out),
    });

    #mkRFn('&force', <x>, 
    #    :foo<bar>,  # prevent it from being inlined
    #-> $x, :$foo! {
    #    mkTypecase($x,
    #        :isinvokable(QAST::Op.new(:op<call>, $x)),
    #        :otherwise(nqp::clone($x))
    #    )
    #});
    

    mkRFn('&force-new', <x>, 
        :foo<bar>,  # prevent it from being inlined
    -> $x, :$foo! {
        mkTypecase($x,
            :isinvokable(QAST::Op.new(:op<call>, nqp::clone($x))),
            :otherwise(nqp::clone($x))
        )
    });
    
    my $tv := Type.Var;
    mkRFn('&delayMemo', <x>, 
        #:returns(Type.Fn(Type.Fn(Type.Void, $tv), Type.Void, $tv)),
        :wasRun(0), :result(NO_VALUE), 
    -> $x, :$wasRun!, :$result! {
        QAST::Block.new(:arity(0),
            mkDeclV(lexVar('foo')),
            mkBind(mkDeclV(lexVar('bar')), nqp::clone($x)),
            QAST::Op.new(:op<if>, $wasRun,
                $result,
                QAST::Stmts.new(
                    mkBind(nqp::clone($wasRun), 1),
                    mkBind(nqp::clone($result), 
                        QAST::Op.new(:op<call>, nqp::clone($x))
                    )
                )
            )
        )
    });

    mkRFn('&ifTag', <subject tag then else>, 
        #:returns(Type.Fn(NQPMu, Type.Str, NQPMu, NQPMu, NQPMu)), 
        :tagAndId(NO_VALUE), 
    -> $subject, $tag, $then, $else, :$tagAndId! {
        my $extract-id-as-Int := mkListLookup(:index(0), # extract id as int from str tagAndId (Note: radix returns an array, not an int!)
            QAST::Op.new(:op<radix>,
                asNode(10),
                nqp::clone($tagAndId),
                asNode(1),
                asNode(0)
            )
        );
        Type.Int.set($extract-id-as-Int);

        mkTypecase($subject,
            :islist(QAST::Stmts.new(
                mkBind($tagAndId, mkListLookup($subject, :index(0))),
                QAST::Op.new(:op<if>,
                    QAST::Op.new(:op<iseq_s>,
                        $tag,
                        QAST::Op.new(:op<substr>, nqp::clone($tagAndId), asNode(0), asNode(1)),
                    ),
                    mkCall($then, $extract-id-as-Int),
                    QAST::Op.new(:op<call>, nqp::clone($else))  # different tag
                )
            )),
            :otherwise(QAST::Op.new(:op<call>, nqp::clone($else)))  # subject not a list
        );
    });
    
    mkRFn('&->#n', <subject tag index>, 
        #:returns(Type.Fn(NQPMu, Type.Str, Type.Int, NQPMu)),
    -> $subject, $tag, $index {
        my $tagStr := cloneAndSubst($tag);
        $tagStr.returns(str);
        QAST::Op.new(:op<call>, lexVar('&ifTag'), $subject, $tag,
            QAST::Block.new(:arity(1),
                lexVar('_', :decl<param>),
                mkListLookup($subject, :index($index))
            ),
            QAST::Block.new(:arity(0),
                mkDie(
                    mkConcat('no such tag: ', $tagStr)
                )
            )
        )
    });

    mkRFn('&strOut', <u indent>, 
        #:returns(Type.Fn(NQPMu, Type.Str, Type.Str)), 
    -> $u, $indent {
        my $v       := lexVar('v');
        my $id      := lexVar('id');
        my $info    := lexVar('info');
        my $src     := lexVar('src', :returns(str));
        my $from    := lexVar('from');
        my $length  := lexVar('length');
        my $fvars   := lexVar('fvars');
        my $fvn2dBI := lexVar('fvn2dBI');  # "free var name 2 deBruijn index"
        my $i       := lexVar('i');
        my $pairStr := lexVar('pairStr');
        my $pair    := lexVar('pair');
        my $name    := lexVar('name', :returns(str));
        my $dBI     := lexVar('dBI');   # "deBruijn index"
        my $dBIStr  := lexVar('dBIStr');
        my $val     := lexVar('val');
    
        mkBind(mkDeclV($v), mkRCall('&force-new', $u)),
        mkTypecase($v,
            #:isinvokable(
            #    mkRCall('&strOut', QAST::Op.new(:op<call>, nqp::clone($v)), nqp::clone($indent))
            #),
            :isstr(
                mkRCall('&strLit', nqp::clone($v))
            ),
            :isint(
                QAST::Op.new(:op<stringify>, nqp::clone($v))    # Attention: works only if under a CompUnit with :hll<nqp> (!!)
            ),
            :isnum(
                QAST::Op.new(:op<stringify>, nqp::clone($v))    # Attention: works only if under a CompUnit with :hll<nqp> (!!)
            ),
            :islist(
                mkRCall('&ifTag', nqp::clone($v), 'λ',
                    QAST::Block.new(:arity(1),
                        mkDeclP($id),
                        mkBind(mkDeclV($fvars),       mkRCall('&sublist', nqp::clone($v), 2)),
                        mkBind(mkDeclV($info),        mkListLookup(lexVar('.λinfo'), :index($id))),
                        mkBind(mkDeclV($fvn2dBI),
                            QAST::Op.new(:op<split>, asNode(' '), mkListLookup($info, :index(3)))
                            #mkListLookup($info, :index(3))
                        ),
                        mkBind(mkDeclV($from),        mkListLookup($info, :index(1))),
                        mkBind(mkDeclV($length),      mkListLookup($info, :index(2))),
                        mkBind(mkDeclV($src),
                            #mkConcat(
                                QAST::Op.new(:op<substr>, lexVar('.src'), $from, $length),
                            #    '  # :tag(', mkRCall('&strLit', mkListLookup(nqp::clone($v), :index(0))), ')',
                            #)
                        ),
                        mkBind(mkDeclV($i), 0),
                        QAST::Op.new(:op<for>, $fvn2dBI, QAST::Block.new(:arity(1),
                            mkDeclP($pairStr),
                            mkBind(mkDeclV($pair), QAST::Op.new(:op<split>, asNode('.'), $pairStr)),
                            mkBind(mkDeclV($name), mkListLookup(nqp::clone($pair),  :index(0))),
                            mkBind(mkDeclV($dBI),  mkListLookup(nqp::clone($pair),  :index(1))),
                            mkBind(mkDeclV($val),  mkListLookup(nqp::clone($fvars), :index($i))),
                            mkBind(nqp::clone($i), QAST::Op.new(:op<add_i>, nqp::clone($i), asNode(1))),
                            mkBind(mkDeclV($dBIStr), 
                                QAST::Op.new(:op<if>, 
                                    QAST::Op.new(:op<not_i>, nqp::clone($dBI)),
                                    asNode('∞'),           # show "∞" as deBruijn index of unbound var
                                    QAST::Op.new(:op<stringify>, nqp::clone($dBI))
                                ),
                            ),
                            mkBind($src,
                                mkConcat($src, 
                                    QAST::Op.new(:op<concat>, asNode("\n"),       nqp::clone($indent)),
                                    QAST::Op.new(:op<concat>, asNode('# where '), nqp::clone($name)),
                                    #'(', $dBIStr, ')',
                                    QAST::Op.new(:op<concat>, asNode(' = '),
                                        QAST::Op.new(:op<if>,
                                            QAST::Op.new(:op<iseq_s>, nqp::clone($name), asNode('self')),
                                            asNode('...'),
                                            mkRCall('&strOut', 
                                                $val,
                                                QAST::Op.new(:op<concat>, nqp::clone($indent), asNode('#           '))
                                            ),
                                        )
                                    )
                                )
                            )
                        )),
                        $src
                    ),
                    mkDelaySimple(QAST::Op.new(:op<reprname>,  nqp::clone($v)))
                )
            ),
            :otherwise(
                QAST::Op.new(:op<reprname>,  nqp::clone($v))
            ),
        );
    });
    
    $tv := Type.Var;
    mkRFn('&say', <u>, 
        #:returns(Type.Fn(Type.Var, Type.Int)),
    -> $u {
        my $v := lexVar('v');
        mkBind(mkDeclV($v), mkRCall('&force-new', nqp::clone($u))),
        QAST::Op.new(:op<say>,
            mkTypecase($v,
                :isstr(
                    nqp::clone($v)
                ),
                :otherwise(
                    mkRCall('&strOut', nqp::clone($v), '')
                ),
            ),
        ),
    });
    
    my $tvIn := Type.Var;
    my $tvOut := Type.Var;
    mkRFn('&apply1', <f a1>,
        #:returns(Type.Fn(Type.Fn($tvIn, $tvOut), $tvIn, $tvOut)),
        :result(NO_VALUE), 
    -> $f, $a1, :$result! {
        my $g := lexVar('g');
        mkBind(mkDeclV($g), mkLambda2code(mkRCall('&force-new', $f))),
        mkTypecase($g,
            :isinvokable(
                QAST::Stmts.new(
                    mkBind($result, QAST::Op.new(:op<call>,
                        nqp::clone($g),
                        nqp::clone($a1)
                    )),
                    mkRCall('&force-new', nqp::clone($result)),
                )
            ),
            :otherwise(
                mkDie(
                    QAST::Op.new(:op<concat>,   :returns(str),
                        QAST::Op.new(:op<concat>, asNode('cannot apply '), mkRCall('&strOut', nqp::clone($g), '')),
                        QAST::Op.new(:op<concat>, asNode(' to '), mkRCall('&strOut', nqp::clone($a1), ''))
                    )
                )
            )
        )
    });
    
    #$block.push(mkBind(lexVar('&testDelay01', :decl<static>),
    #    mkDelayMemo(mkDelaySimple(
    #        QAST::Stmts.new(:returns(int),
    #            QAST::Op.new(:op<say>, asNode('&testDelay01 forced!!!!')),
    #            asNode('42')
    #        )
    #    ))
    #));

    #mkRFn('&testDelay02', <delayed>, :simple(nqp::null), :memo(nqp::null), -> $delayed, $simple, $memo {
    #    mkBind($simple, mkDelaySimple($delayed)),
    #    mkBind($memo,   mkDelayMemo($delayed)),
    #    
    #    #$simple
    #    $memo
    #});

    $block;
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

sub lookup(str $name, *@blocks) {
    my $n := +@blocks;
    my $i := 0;
    my %out;

    while ($i < $n) && (nqp::elems(%out) == 0) {
        %out := @blocks[$i].symbol($name);
        $i++;
    }
    %out;
}

sub typesubst($n, %substitution) {
    TreeWalk.dfs-up(
        -> $n, @p {
            my $type := Type.of($n);
            TreeWalkDo.recurse(:take($type && $type.vars));
        },
        -> $n, @p {
            Type.of($n).subst(%substitution).set($n);
        },
        $n
    );
}

sub ignore(*@ps, *%ns) {
    say('!!!!', join('', @ps, :map(-> $_ { istype($_, Type, TypeConstraint) ?? $_.Str !! $_ } )));
    TypeConstraint.False;
}


sub fresh-var(:%new-vars!) {
    my $v := Type.Var;
    %new-vars{$v.name} := $v;
    $v;
}

sub typecheck-application($tCallee, @tArgs, :$currentBlock!, :%new-vars!, :@constraints!, :$at!, :$callee) {
    Type.insist-isValid($tCallee);
    for @tArgs {
        if $_.isVoid || $_.isCrossType {
            Type.error(
                :$at, 
                'cannot have Cross/Void in arg position (while applying ', $callee, ' ::', $tCallee, ")\n"
                ~ '...got ' ~ $_.Str
            );
        }
    }
    my $tArgs := Type.Cross(|@tArgs);   # << TODO: only if necessary
    my $c := TypeConstraint.False;
    my $tOut;
    if $tCallee.isTypeVar {
        $tOut := fresh-var(:%new-vars);
        $c := Type.constrain-sub($tCallee, Type.Fn(Type.Cross(|@tArgs), $tOut));
        
        #nqp::die("NYI: typecheck-application(" ~ $tCallee.Str ~ ', [' ~ join(', ', @tArgs, :map(-> $t { $t.Str })) ~ ']'
        #    ~ ', ..., :callee(' ~ describe($callee) ~ '))'
        #    ~ "\nunder constraints " ~ TypeConstraint.And(|@constraints).Str
        #    ~ "\n" ~ dump($currentBlock)
        #);
    } elsif $tCallee.isFnType || $tCallee.isForallType {
        my $n := nqp::elems(@tArgs);
        if $n == 0 {
            @tArgs.push(Type.Void);
            $n := 1;
        }
        $c := TypeConstraint.True;
        my $tF;
        my $tIn;
        my %quantified-vars := {};
        if $tCallee.isForallType {
            $tF := $tCallee.body;
            for $tCallee.bound-vars {
                %quantified-vars{$_.key} := $_.value;
            }
        } else {    # $tCallee.isFnType
            $tF := $tCallee;
        }
        $tIn  := $tF.in;
        $tOut := $tF.out;
        
        my @tIn := $tIn.isCrossType
            ?? $tIn.foldl(-> $acc, $t { $acc.push($t); $acc; }, [])
            !! [$tIn];
        my @abstraction-vars := [];
        if $n == nqp::elems(@tIn) {
            my $i := 0;
            for @tIn {
                my $t := $_;
                my $tArg := @tArgs[$i];
                if $tArg.isForallType { # instantiate with all bound vars fresh
                    my %s := {};
                    for $tArg.bound-vars {
                        my $v := fresh-var(:%new-vars);
                        @abstraction-vars.push($v);
                        %s{$_.key} := $v;
                    }
                    $tArg := $tArg.body.subst(%s);
                }
                $i++;
                $c := TypeConstraint.And($c, Type.constrain-sub($tArg, $t, :$at, :onError(&ignore)));
            }
            my $s := $c.unify(:for(%quantified-vars));
            $c := $c.subst($s);
            my %fv-in-c := $c.vars;
            my %additional := {};
            for %quantified-vars {
                if nqp::existskey(%fv-in-c, $_.key) {
                    %additional{$_.key} := fresh-var(:%new-vars);    # ??????? add to @abstraction-vars?
                }
            }
            if %additional {
                $c := $c.subst(%additional);
                $s := concat-subst($s, %additional);
            }
            $tOut := $tOut.subst($s).forall(|@abstraction-vars, |%quantified-vars);
        } else {
            Type.error(:$at, 'wrong arity: cannot apply ', $callee, ' ::', $tCallee, '  to  ', $tArgs);
        }
    } elsif $tCallee.isSumType {
        my @cs    := [];
        my @tOuts := [];
        $tCallee.foreach(-> $t {
            my $tOut;
            my @constraints := [];
            try {
                $tOut := typecheck-application($t, @tArgs, :$currentBlock, :@constraints, :%new-vars, :$at, :$callee);
                my $c := nqp::elems(@constraints) == 0 ?? TypeConstraint.True !! @constraints[0];
                unless $c.isFalse {
                    @cs.push($c);
                    @tOuts.push($tOut);
                }
            }
        });
        if @cs {
            $c := TypeConstraint.Or(|@cs);
            $tOut := Type.Sum(|@tOuts);
        }
        #if +@cs == 1 {
        #    $tOut := @tOuts[0];
        #    $c := @cs[0];
        #} elsif +@cs > 1 {
        #    Type.error(:$at, 'cannot apply ', $callee, ' ::', $tCallee, '  to  ', $tArgs, ' - ambiguous: ' ~ TypeConstraint.Or(|@cs));
        #}
    }
    if $c.isFalse {
        Type.error(:$at, 'cannot apply ', $callee, ' ::', $tCallee, '  to  ', $tArgs);
    } elsif $c.isTrue {
        # nothing
    } else {
        @constraints.push($c);
        say('>>Type-constraint: ', $c.Str);
    }
    $tOut;
}

class LActions is HLL::Actions {
    has @!lambdaInfo;

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

        my $runtime := make-runtime();
        $top-block.push($runtime);
        
        my $lambdaInfo := mkList();
        for @!lambdaInfo {
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
        $top-block.unshift(
            mkBind(lexVar('.λinfo', :decl<static>), $lambdaInfo)
        );

        $top-block.unshift(
            mkBind(lexVar('.src', :decl<static>), ~$/)
        );

        my $dummy-block := QAST::Block.new;
        my %new-vars := {};
        {
            self.typecheck($top-block, $dummy-block, :%new-vars);              # <<<<<<<<< TODO
            CATCH {
                say(~$!);
                nqp::rethrow($!);# unless nqp::index(~$!, 'Type Error: NYI') == 0;
            }
        }


        #my $mainTermType;
        #$mainTermType := self.typecheck($mainTerm, QAST::Block.new);
        #say('MAIN type: ' ~ typeToStr($mainTermType));

        # Note: cannot use mkBind here since this enforces an init value
        my $quastSizeBinding  := QAST::Op.new(:op<bind>, lexVar('.qastSize',   :decl<static>));   # will receive a value node later
        my $blockCountBinding := QAST::Op.new(:op<bind>, lexVar('.blockCount', :decl<static>));   # will receive a value node later
        my $listCountBinding  := QAST::Op.new(:op<bind>, lexVar('.listCount',  :decl<static>));   # will receive a value node later
        my $ivalCountBinding  := QAST::Op.new(:op<bind>, lexVar('.ivalCount',  :decl<static>));   # will receive a value node later
        my $svalCountBinding  := QAST::Op.new(:op<bind>, lexVar('.svalCount',  :decl<static>));   # will receive a value node later
        my $svalSizeBinding   := QAST::Op.new(:op<bind>, lexVar('.svalSize',   :decl<static>));   # will receive a value node later
        my $s := $top-block;
        $s.push($quastSizeBinding);
        $s.push($blockCountBinding);
        $s.push($listCountBinding);
        $s.push($ivalCountBinding);
        $s.push($svalCountBinding);
        $s.push($svalSizeBinding);
        
        my $mainResult := locVar('mainResult');
        $s.push(QAST::Block.new(:blocktype<immediate>,
            mkDeclV($mainResult),
            #mkRCall('&say', mkConcat(
            #    ~nqp::elems(@!lambdaInfo), " lambdas\n",
            #    lexVar('.qastSize'), " QAST::Node s\n",
            #    lexVar('.blockCount'), " QAST::Block s\n",
            #    lexVar('.listCount'), " QAST::Op(list) s\n",
            #    lexVar('.ivalCount'), " QAST::IVal s\n",
            #    lexVar('.svalSize'), " chars ttl in ", lexVar('.svalCount'), " QAST::SVal s\n",
            #    "------------------------------------------------",
            #)),

            #QAST::Op.new(:op<flushfh>, QAST::Op.new(:op<getstdout>)),
            
            #mkRCall('&say', mkConcat('&testDelay02 = ', mkRCall('&testDelay02', lexVar('&testDelay01')))),
            #mkRCall('&say', mkConcat('&testDelay02 = ', mkRCall('&testDelay02', lexVar('&testDelay01')))),
            
            mkBind($mainResult, mkRCall('&strOut', $mainTerm, '')),
            
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

    sub typecheck-var($n, $currentBlock, *@moreBlocks, :%new-vars!, :@constraints!) {
        insist-isa($n, QAST::Var);
        if $n.decl {
            my $decl := lookup($n.name, $currentBlock)<declaration>;
            if $decl {
                Type.error(:at($n), 'redeclaration of ', $n, "in \n", dump($currentBlock, :indent('    ')));
            } else {
                $currentBlock.symbol($n.name, :declaration($n));
                unless Type.of($n) {
                    fresh-var(:%new-vars).set($n);
                };
                if $n.decl eq 'param' {
                    $currentBlock.ann('slurpy').push($n) if $n.slurpy;
                    $currentBlock.ann('optional').push($n) if $n.default;
                    if $n.named {
                        $currentBlock.ann('named'){$n.name} := $n;
                    } else {
                        my @positional := $currentBlock.ann('positional');
                        $n.annotate('positional_index', +@positional);
                        @positional.push($n);
                    }
                }
            }
        } else {
            my $decl := lookup($n.name, $currentBlock, |@moreBlocks)<declaration>;
            if $decl {
                my $tDecl := Type.of($decl);
                if $tDecl {
                    my $tVar := Type.of($n);
                    if $tVar {
                        my $c := Type.constrain-sub($tVar, $tDecl,
                            :onError(-> :$at, *@msgPieces {
                                Type.error(:at($n), 'mismatch of use-type and declaration-type: ', $tVar.Str, ' !:< ', $tDecl.Str, " in \n", dump($currentBlock));
                            })
                        );
                        @constraints.push($c);
                    } else {
                        $tDecl.set($n);
                    }
                } else {
                    Type.error(:at($n), 'still untyped: declaration for ', $n);
                }
            } else {
                Type.error(:at($n), 'no declaration found for ', $n, "\n", dump($currentBlock));
            }
        }
        Type.of($n);
    }

    method typecheck-typecase($n, $currentBlock, *@moreBlocks, :%new-vars!, :@constraints = []) {
        nqp::die("expected an Op(typecase) - got " ~ describe($n))
            unless isOp($n, 'typecase');
        my $subject-name := $n.name;
        Type.error(:at($n), 'no :name for ', $n, " in\n", dump($currentBlock))
            unless nqp::isstr($subject-name);
        my %clauses := {};
        my @args := $n.list;
        for @args {
            my $arg-name := $_.named;
            Type.error(:at($n), 'no :named for ', $_, "\n", dump($n))
                unless nqp::isstr($arg-name);
            Type.error(:at($n), 'duplicate typecase clause :named<', $arg-name, '>: ', $_, "\n", dump($n))
                if nqp::existskey(%clauses, $arg-name);
            %clauses{$arg-name} := $_;
            $_.named(nqp::null_s);
        }
        my $outer-subject-type := self.typecheck(lexVar($subject-name), $currentBlock, |@moreBlocks, :%new-vars, :@constraints);
        my $tFn := Type.Fn(fresh-var(:%new-vars), fresh-var(:%new-vars));
        
        my %subject-type-otherwise := nqp::hash(
            Type.Int.Str,   Type.Int,
            Type.Num.Str,   Type.Num, 
            Type.Str.Str,   Type.Str,
            Type.BOOL.Str,  Type.BOOL,
            Type.Array.Str, Type.Array,
            $tFn.Str,       $tFn,
        );
        my %op-to-type := nqp::hash(
            'isint', Type.Int,
            'isnum', Type.Num,
            'isstr', Type.Str,
            'islist', Type.Array,
            'isinvokable', $tFn,
        );
        my sub typecheck-clause($clause-body, $inner-subject-type) {
            my $decl := lexVar($subject-name, :decl<var>);
            my $c := TypeConstraint.True;
            $c := Type.constrain-sub(:at($clause-body), $inner-subject-type, $outer-subject-type);
            $inner-subject-type.set($decl);
            unless $c.isTrue {
                @constraints.push($c);
                $clause-body.annotate('constraints', $c.Str);
            }
            my $body := QAST::Block.new($clause-body);
            $body.symbol($subject-name, :declaration($decl));
            my $tBody := self.typecheck($clause-body, $body, $currentBlock, |@moreBlocks, :%new-vars, :@constraints);
            $tBody.set($clause-body);
        }
        my $otherwise := %clauses<otherwise>;
        nqp::deletekey(%clauses, 'otherwise');
        my $out := $otherwise;
        
        for %clauses {
            my $k := $_.key;
            my $v := $_.value;
            my $inner-subject-type := %op-to-type{$k};
            Type.error(:at($n), 'invalid typecase clause :named<', $k, '>: ', $v, "\n", dump($n))
                unless $inner-subject-type;
            nqp::deletekey(%subject-type-otherwise, $inner-subject-type.Str);
            
            typecheck-clause($v, $inner-subject-type);

            my $subject := lexVar($subject-name);
            $outer-subject-type.set($subject);
            my $test := QAST::Op.new(:op($k), $subject);
            Type.BOOL.set($test);
            $out := QAST::Op.new(:op<if>,
                $test,
                $v,
                $out
            );
        }

        my @subject-type-otherwise := [];
        @subject-type-otherwise.push($_.value) # collect remaining type possibilities in otherwise branch
            for %subject-type-otherwise;
        
        typecheck-clause($otherwise, Type.Sum(|@subject-type-otherwise));
        
        $n.op('if');
        $n.name(nqp::null_s);
        $n.set_children($out.list);
        say('>>>>>>>>>> final typecheck of $n: ', TypeConstraint.And(|@constraints).Str, "\n", dump($n));
        self.typecheck($n, $currentBlock, |@moreBlocks, :%new-vars, :@constraints);
        say('>>>>>>>>>>', dump($n));
    }

    method typecheck($n, $currentBlock, *@moreBlocks, :%new-vars!, :@constraints = []) {
        if isVar($n) {
            typecheck-var($n, $currentBlock, |@moreBlocks, :%new-vars, :@constraints);
        } elsif !Type.of($n) {  # otherwise do typecheck only if $n doesn't already have a type
            if isSVal($n) {
                Type.Str.set($n);
            } elsif isIVal($n) {
                Type.Int.set($n);
            } elsif isNVal($n) {
                Type.Num.set($n);
            } elsif isLambda($n) {
                my $block   := $n[1];
                my $binder  := $block[0];
                my $body    := $block[1];
                my @bound   := $body.ann('FV'){$binder.name} // [];

                my $tBinder;
                my $tBody;
                if @bound {
                    $tBinder := Type.Var;
                    for @bound {
                        $tBinder.set($_);
                    }
                } else {    # binder is ignored
                    $tBinder := Type._;
                }
                $tBody := self.typecheck($body, $block, $currentBlock, :%new-vars, |@moreBlocks);

                $tBinder.set($binder);
                Type.Fn($tBinder, $tBody).set($n);
            } elsif isApp($n) {
                my $fun := $n[0];
                my $arg := $n[1];
                my $tFun := self.typecheck($fun, $currentBlock, |@moreBlocks, :%new-vars);
                my $tArg := self.typecheck($arg, $currentBlock, |@moreBlocks, :%new-vars);
                if $tFun.isFnType {
                    my $c := Type.constrain(:at($n), $tFun.in, $tArg);
                    say('>>Type-constraint: ', $c.Str) unless $c.isTrue;
                    $tFun.out.set($n);
                } elsif $tFun.isTypeVar {
                    my $tOut := TypeVar.new;
                    my $c := Type.constrain(:at($n), $tFun, Type.Fn($tArg, $tOut));
                    say('>>Type-constraint: ', $c.Str) unless $c.isTrue;
                    $tOut.set($n);
                } else {
                    say(dump($n));
                    Type.error(:at($n), 'cannot apply ', $tFun, ' to ', $tArg);
                }
            #} elsif isRCall($n) {
            #    my $tRuntimeFn := %runtime-fns-types{$n.name};
            #    my @tArgs := [];
            #    @tArgs.push(self.typecheck($_, $currentBlock, |@moreBlocks, :%new-vars))
            #        for $n.list;
            #
            #    my $temp := $tRuntimeFn;
            #    for @tArgs {
            #        if $temp.isFnType {
            #            my $c := Type.constrain(:at($n), $temp.in, $_);
            #            say('>>Type-constraint: ', $c.Str) unless $c.isTrue;
            #            $temp := $temp.out;
            #        } elsif $temp.isTypeVar {
            #           my $next := Type.Fn($_, Type.Var);
            #           my $c := Type.constrain(:at($n), $temp, $next);
            #            say('>>Type-constraint: ', $c.Str) unless $c.isTrue;
            #            $temp := $next.out;
            #        } else {
            #            say(dump($n));
            #            Type.error(:at($n), 'cannot apply runtime fn (', $n.name, ':', $tRuntimeFn, ') to',
            #                join(' (', @tArgs, :map(-> $t { $t.Str }), :prefix1st), ')'
            #            );
            #        }
            #    }
            #    $temp.set($n);
            } elsif istype($n, QAST::Stmts, QAST::Stmt) {
                my $tLast := Type.Void;
                $tLast := self.typecheck($_, $currentBlock, |@moreBlocks, :%new-vars, :@constraints)
                    for $n.list;
                $tLast.set($n);
            } elsif istype($n, QAST::Block) {
                #say('>>>>typechecking Block');
                #say(dump($n));
                $n.annotate('positional', []);
                $n.annotate('named',      {});
                $n.annotate('slurpy',     []);
                $n.annotate('optional',   []);
                my $tOut;
                my %child-new-vars := {};
                my @child-constraints := [];
                for $n.list {
                    $tOut := self.typecheck($_, $n, $currentBlock, |@moreBlocks, :new-vars(%child-new-vars), :constraints(@child-constraints));
                }
                if $n.ann('named') || $n.ann('slurpy') || $n.ann('optional') {
                    Type.error(:at($n), 'NYI: typechecking named/slurpy/optional params', ":\n", dump($n, :indent("    ")));
                }
                my @tIns := [];
                for $n.ann('positional') {
                    @tIns.push(Type.of($_));
                }
                my $tBlock := Type.Fn(Type.Cross(|@tIns), $tOut);
                $tBlock.set($n);
                my $tSelf := $n.ann('constrain-self');
                if $tSelf {
                    my $cSelf := Type.constrain(:at($n), $tSelf, $tBlock);
                    @child-constraints.push($cSelf);
                    say('>>Type-constraint(recursion): ', $cSelf.Str);
                }
                my $c := TypeConstraint.And(|@child-constraints);
                say('>>unifying ', $n.name, ': ', $c.Str);
                {
                    my %s := $c.unify(:for(%child-new-vars));
                    $c := $c.subst(%s);
                    say('   yielded ', subst-to-Str(%s), '; ', $c.Str);
                    @constraints.push($c);
                    for %child-new-vars {
                        unless nqp::existskey(%s, $_.key) {
                            %new-vars{$_.key} := $_.value;
                        }
                    }
                    $n.annotate('constraints', $c.Str)
                        unless $c.isTrue;
                    typesubst($n, %s);
                    # finally abstract over all remaining type vars
                    Type.of($n).forall(%child-new-vars).set($n);
                    say(dump($n));
                    CATCH {
                        say(~$_);
                        say(dump($n));
                        nqp::rethrow($_);
                    }
                }
            } elsif isOp($n) {
                if $n.op eq 'bind' {
                    my $var := $n[0];
                    my $val := $n[1];

                    my $tVar := self.typecheck($var, $currentBlock, |@moreBlocks, :%new-vars, :@constraints);
                    if istype($val, QAST::Block) {
                        panic($n.node, 'NYI: bind Block ' ~ dump($n))
                            unless ($val.blocktype eq '') || ($val.blocktype eq 'declaration');
                        $val.annotate('constrain-self', $tVar);
                    }
                    my $tVal := self.typecheck($val, $currentBlock, |@moreBlocks, :%new-vars, :@constraints);
                    if $var.decl {
                        $tVal.set($var);
                    } else {
                        my $c := Type.constrain(:at($n), $tVar, $tVal);
                        @constraints.push($c);
                        say('>>Type-constraint(bind "' ~ $var.name ~ '"): ', $c.Str) unless $c.isTrue;
                    }
                    
                    $tVal.set($n);
                    if istype($val, QAST::Block) {
                        my $c := $val.ann('constraints');
                        say('>>typed Block ' ~ $var.name ~ ':: ' ~ $tVal ~ '; ' ~ $c);
                        $n.annotate('constraints', $c);
                    }
                } elsif $n.op eq 'typecase' {
                    self.typecheck-typecase($n, $currentBlock, |@moreBlocks, :%new-vars, :@constraints);
                } else {
                    my @tArgs := [];
                    @tArgs.push(self.typecheck($_, $currentBlock, |@moreBlocks, :%new-vars, :@constraints))
                        for $n.list;
                    
                    if $n.op eq 'list' {
                        Type.Array.set($n);
                    } elsif ($n.op eq 'call') || ($n.op eq 'callstatic') {
                        my $callee;
                        my $tCallee;
                        my $name := $n.name;
                        if $name {
                            $callee := lexVar($name);
                            $tCallee := self.typecheck($callee, $currentBlock, |@moreBlocks, :%new-vars);
                        } elsif +$n.list >= 1 {
                            $callee := $n.list[0];
                            $tCallee := @tArgs.shift;
                            $name := $callee.name;
                        } else {
                            Type.error(:at($n), 'no callee for ', $n);
                        }
                        my $tOut := typecheck-application(:at($n), :callee($name), $tCallee, @tArgs, :$currentBlock, :%new-vars, :@constraints);
                        #say('>>Type-constraint/', $n.op, ': ', $callee.name, ': ', $c.Str) unless $c.isTrue;
                        $tOut.set($n);
                    } else {
                        my $tOp := Type.ofOp($n.op);
                        if $tOp {
                            my $tOut := typecheck-application(:at($n), :callee('Op ' ~ $n.op), $tOp, @tArgs, :$currentBlock, :%new-vars, :@constraints);
                            $tOut.set($n);
                        } else {
                            say("\n", dump($currentBlock));
                            say("\n", dump($n));
                            Type.error(:at($n), 'dunno type of ', $n);
                        }
                    }
                }
            } else {
                say("\n", dump($n));
                Type.error(:at($n), 'typecheck NYI: ', $n);
            }
        }
        Type.of($n);
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

        my $out := mkRCall('&apply1', $f, mkDelayMemo($a));
        
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

    my %str-esc := nqp::hash(
        '"', '"',
        '\\', '\\',
        'b', "\b",
        'r', "\r",
        'n', "\n",
        'f', "\f",
        't', "\t",
    );

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
        $out.node($/);
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


    method abstraction($/) {
        my $binder := mkDeclP(lexVar(~$/<varName>, :node($/<varName>)));
        my $body   := $/<body>.ast;
        
        my $out := mkLambda($binder, $body, @!lambdaInfo);
        $out.node($/);
        make $out;
    }

    sub mkLambda($binder, $body, @lambdaInfo) {
        insist-isa($binder, QAST::Var);
        nqp::die("expected var decl - got " ~ dump($binder, :oneLine))
            unless $binder.decl eq 'param';
        insist-isa($body, QAST::Node);

        if !$body.has_ann('FV') {
            nqp::die("missing annotation 'FV' in body\n" ~ $body.dump);
        }

        my $code := QAST::Block.new(:arity(1), :node($body.node), $binder, $body);
        
        my $infoIdx := nqp::elems(@lambdaInfo);
        my $out := mkList(
            asNode('λ' ~ $infoIdx),
            $code
            # free vars will be added below
        );
        $body.annotate('parent', $out);
        $out.annotate('infoIdx', $infoIdx);

        my $from   := nqp::sub_i($binder.node.from, 1); # using nqp::sub_i in order to get an int
        my $length := nqp::sub_i($body.node.to, $from);
        my %info := hash(
            :lambda($out),
            :binder($binder),
            :$from,
            :$length,
            :fvn2dBI({}), # free-var-names-to-deBruijn-indices will be inserted below
            #:node($/), # ???????????????
        );
        @lambdaInfo.push(%info);

        

        my %fvs := copy-free-vars(:into($out), $body);
        my @boundVars := nqp::defor(%fvs{$binder.name}, []);
        nqp::deletekey(%fvs, $binder.name);

        for @boundVars -> $bv {
            my int $i := 0;
            my $p := $bv;
            my @lambdaParents := [];
            $bv.returns($binder.returns);
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
                    my %info := @lambdaInfo[$lp.ann('infoIdx')];
                    %info<fvn2dBI>{$bv.name} := $i;
                }

                # TODO: only in direct parent where it's free (if any)
                #my $directLambdaParent := @lambdaParents[0];
                #my %info := @lambdaInfo[$lp.ann('infoIdx')];
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
                        nqp::die($name ~ ' already maps to ' ~ %fvn2dBI{$name} ~ ' in ' ~ $/)   # !!!! don't have $/ here
                            if nqp::existskey(%fvn2dBI, $name);
                        %fvn2dBI{$name} := 0;   # Note: we're coming bottom up, so the deBruijn index is not yet known
                                                #       it will be updated by the lambda that binds v
                    }
                    $i++;
                }
            }
        }
        
        $out.returns(NQPMu);
        $out;
    }

    method simple-let($/) {
        my @bindings := $/<bindings>;
        my $out := $/<body>.ast;    # the let's body
        
        my $i := +@bindings;
        while $i > 0 {
            my $binding := @bindings[--$i];
            my $binder := $binding<binder>.ast;
            $binder.decl('param');
            my $body   := $binding<body>.ast;
            $out := mkApp(mkLambda($binder, $out, @!lambdaInfo), $body);
            $out.node($/);  # !!?!?!?!
        }
        make $out;
    }

}




sub MAIN(*@ARGS) {
    my $n := lexVar('foo');
    Type.Fn(Type.Void, Type.Int).set($n);
    say(dump($n));


    say((Type.Fn(Type.Str, Type.Int) =:= Type.Fn(Type.Int, Type.Str) ?? 'not ' !! '') 
        ~ 'ok 42 - *NOT* (Type(Str -> Int) =:= Type(Int -> Str))');
    say((Type.Fn(Type.Str, Type.Int) =:= Type.Fn(Type.Str, Type.Int) ?? '' !! 'not ') 
        ~ 'ok 43 - (Type(Str -> Int) =:= Type(Str -> Int))');


    #say(isSVal(QAST::Block.new));
    #say(isSVal(QAST::SVal.new));
    #say(isSVal("asdf"));

    say(isOp(QAST::Block.new));
    say(isOp(QAST::Op.new(:op<bind>)));
    say(isOp(QAST::Op.new(:op<bind>), "null"));
    say(isOp(QAST::Op.new(:op<bind>), "bind"));

    say('---------------------');
    my $v2 := Type.Var;
    my $v3 := Type.Var;
    my $v4 := Type.Var;
    my $v5 := Type.Var;
    my $v6 := Type.Var;
    my $tCallee;
    my @tArgs;
    my %quantified-vars;
    my %new-vars;
    my @cs;
    my $t;

    $tCallee := Type.Fn(Type.Cross(Type.Fn(Type.Cross($v2, $v3), $v5), $v2), Type.Fn($v6, $v2, $v3, $v5)).forall(
        $v2, $v3
    );
    @tArgs := [
        Type.Fn(Type.Cross($v4, Type.Num), Type.Int),
        Type.Str,
    ];
    say('applying ' ~ $tCallee.Str ~ '  to  ' ~ Type.Cross(|@tArgs).Str);
    @cs := [];
    $t := typecheck-application(
        $tCallee,
        @tArgs,
        :currentBlock(), :at(QAST::Block.new), :callee<&curry>,
        :%new-vars,
        :constraints(@cs)
    );
    say($t.Str);
    say(TypeConstraint.And(|@cs).Str);
    say('---------------------');

    $tCallee := Type.Fn(Type.Cross(Type.Fn($v2, $v3), $v2), $v3).forall(
        $v2, $v3
    );
    @tArgs := [
        $v4,
        Type.Int,
    ];
    %quantified-vars := nqp::hash($v2.name, 1, $v3.name, 1);
    say('applying ' ~ $tCallee.Str ~ '  to  ' ~ Type.Cross(|@tArgs).Str);
    @cs := [];
    $t := typecheck-application(
        $tCallee,
        @tArgs,
        :currentBlock(), :at(QAST::Block.new), :callee<&apply1>,
        :%new-vars,
        :constraints(@cs)
    );
    say($t.Str);
    say(TypeConstraint.And(|@cs).Str);
    say('---------------------');

    $tCallee := Type.Fn(Type.Fn($v3, $v4), Type.Fn($v2, $v3), $v2, $v4).forall(
        $v2, $v3, $v4
    );
    @tArgs := [
        $v2,
        #Type.Fn($v2, Type.Int, $v2).forall($v2),
    ];
    say('applying ' ~ $tCallee.Str ~ '  to  ' ~ Type.Cross(|@tArgs).Str);
    @cs := [];
    $t := typecheck-application(
        $tCallee,
        @tArgs,
        :currentBlock(), :at(QAST::Block.new), :callee<&B>,
        :%new-vars,
        :constraints(@cs)
    );
    say($t.Str);
    say(TypeConstraint.And(|@cs).Str);
    say('---------------------');

    $tCallee := Type.Fn(Type.Fn(Type.Void, $v2), Type.Fn($v3, $v2)).forall(
        $v2, $v3
    );
    say($tCallee.Str);
    my $vY := $tCallee.bound-vars<Y>;
    say($tCallee.body.out.forall($vY).Str);
    say('---------------------');

}
