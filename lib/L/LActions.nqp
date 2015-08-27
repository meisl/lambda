use NQPHLL;

use Util;
use Util::QAST;

my class NO_VALUE {}




my class Type {

    method new(*@args, *%adverbs) {
        nqp::die('cannot instantiate class Type');
    }

    method set($n) {
        insist-isa($n, QAST::Node);
        nqp::die('cannot use method set on class Type; need a Type instance')
            unless nqp::isconcrete(self);
        $n.annotate('ty', self);
    }

    # must put methods before subclasses s.t. they're are inherited
    # however, we need to call the subs defined *after* the subclasses
    method isVoid()      { isVoid(self)      }
    method isStrType()   { isStrType(self)   }
    method isIntType()   { isIntType(self)   }
    method isNumType()   { isNumType(self)   }
    method isBoolType()  { isBoolType(self)  }

    method isArrayType() { isArrayType(self) }
    
    method isTypeVar()   { isTypeVar(self)   }
    method isFnType()    { isFnType(self)    }
    method isSumType()   { isSumType(self)   }

    # native types (corresponding to NQP's str, int, num)

    my class Str is Type {
        method Str() { "Str" }
    }
    my $Str := nqp::create(Str);
    method Str() { $Str }


    my class Int is Type {
        method Str() { "Int" }
    }
    my $Int := nqp::create(Int);
    method Int() { $Int }


    my class Num is Type {
        method Str() { "Num" }
    }
    my $Num := nqp::create(Num);
    method Num() { $Num }


    # the Array type (corresponding to NQP's NQPArray)

    my class Array is Type {
        method Str() { "Array" }
    }
    my $Array := nqp::create(Array);
    method Array() { $Array }


    # the Bool type

    my class Bool is Type {
        method Str() { "Bool" }
    }
    my $Bool := nqp::create(Bool);
    method BOOL() { $Bool }


    # the Void type, only to be used in Fn types

    my class Void is Type {
        method Str() { "Void" }
    }
    my $Void := nqp::create(Void);
    method Void() { $Void }


    # the DontCare type, to be used for ignored parameters

    my class DontCare is Type {
        method Str() { "_" }
    }
    my $DontCare := nqp::create(DontCare);
    method DontCare() { $DontCare }
    method _() { $DontCare }


    # type variables

    my %type-vars := {};
    my class Var is Type {
        has $!name;
        method new() {
            my $name := 't' ~ nqp::elems(%type-vars);
            my $instance := nqp::create(self);
            nqp::bindattr($instance, self, '$!name', $name);
            %type-vars{$name} := $instance;
            $instance;
        }
        method Str() { $!name }
    }
    method Var() { Var.new }


    # function types

    my %fn-types := {};
    my class Fn is Type {
        has $!in;
        has $!out;
        has $!str;
        method new($in, $out) {
            my $str := toStr($in, :parens) ~ ' -> ' ~ toStr($out);
            my $instance := %fn-types{$str};
            unless $instance {
                $instance := nqp::create(self);
                nqp::bindattr($instance, self, '$!in',  $in);
                nqp::bindattr($instance, self, '$!out', $out);
                nqp::bindattr($instance, self, '$!str', $str);
                %fn-types{$str} := $instance;
            }
            $instance;
        }
        method Str() { $!str }
        method in()  { $!in  }
        method out() { $!out }
    }
    method Fn($a, $b, *@more) {
        @more.unshift($b);
        @more.unshift($a);
        my $out := @more.pop;
        while @more {
            $out := Fn.new(@more.pop, $out);
        }
        $out;
    }


    # sum types

    my %sum-types := {};
    my class Sum is Type {
        has $left;
        has $right;
        has $!str;
        method new($left, $right) {

            my $str := toStr($left, :parens) ~ ' + ' ~ toStr($right, :parens);
            my $instance := %fn-types{$str};
            unless $instance {
                $instance := nqp::create(self);
                nqp::bindattr($instance, self, '$!left',  $left);
                nqp::bindattr($instance, self, '$!right', $right);
                nqp::bindattr($instance, self, '$!str',   $str);
                %fn-types{$str} := $instance;
            }
            $instance;
        }
        method Str() { $!str }
    }


    my sub isVoid($t)      { $t =:= Type.Void  }
    my sub isStrType($t)   { $t =:= Type.Str   }
    my sub isIntType($t)   { $t =:= Type.Int   }
    my sub isNumType($t)   { $t =:= Type.Num   }
    my sub isBoolType($t)  { $t =:= Type.BOOL  }
    my sub isArrayType($t) { $t =:= Type.Array }
    my sub isTypeVar($t)   { nqp::istype($t, Var) }
    my sub isFnType($t)    { nqp::istype($t, Fn)  }
    my sub isSumType($t)   { nqp::istype($t, Sum) }

    my sub toStr($t, :$parens) {
        nqp::die('invalid type argument ' ~ describe($t))
            unless nqp::istype($t, Type) && nqp::isconcrete($t);
        if $t.isFnType && $parens {
            '(' ~ $t.Str ~ ')';
        } else {
            $t.Str;
        }
    }

    my %op-types := nqp::hash(
        # special (not listed here, but explicitly handled by typecheck)
        #'bind' # how to type the var argument?
        #'list' # due to arbitrary nr of args
        #'hash' # due to arbitrary nr of args (although some constraints, eg even nr of args)
        
        # str
        'concat', Type.Fn($Str,   $Str, $Str),
        'escape', Type.Fn($Str,   $Str),
        # int
        'iseq_i', Type.Fn($Int,   $Int, $Bool),
        'isne_i', Type.Fn($Int,   $Int, $Bool),
        'isgt_i', Type.Fn($Int,   $Int, $Bool),
        'isge_i', Type.Fn($Int,   $Int, $Bool),
        'islt_i', Type.Fn($Int,   $Int, $Bool),
        'isle_i', Type.Fn($Int,   $Int, $Bool),
        'add_i',  Type.Fn($Int,   $Int, $Int),
        'sub_i',  Type.Fn($Int,   $Int, $Int),
        # list/hash
        'elems',  Type.Fn($Array, $Int),
    );
    method ofOp($op) {
        unless nqp::isstr($op) {
            nqp::die('expected a str - got ' ~ describe($op));
        }
        %op-types{$op};
    }
    
    
    method of($n) {
        insist-isa($n, QAST::Node);
        $n.ann('ty');
    }

}

my class Void is Type {

    method new(*@args, *%adverbs) {
        nqp::die('cannot instantiate Void');
    }
}

my class FnType is Type {
    has $!in;
    has $!out;
    has $!str;

    method in()  { $!in }
    method out() { $!out }
    method Str() { $!str }

    my %instances := {};

    method new($in, $out) {
        my $str := typeToStr($in, :parens) ~ ' -> ' ~ typeToStr($out);
        my $instance := %instances{$str};
        unless $instance {
            $instance := nqp::create(self);
            nqp::bindattr($instance, FnType, '$!in', $in);
            nqp::bindattr($instance, FnType, '$!out', $out);
            nqp::bindattr($instance, FnType, '$!str', $str);
            %instances{$str} := $instance;
        }
        $instance;
    }
    

}

my class TypeVar is Type {
    has $!name;

    my %instances := {};

    method new() {
        my $name := 't' ~ nqp::elems(%instances);
        my $instance := nqp::create(self);
        nqp::bindattr($instance, TypeVar, '$!name', $name);
        %instances{$name} := $instance;
        $instance;
    }

    method Str() { $!name }

}


my sub typeToStr($t, :$parens) {
    if nqp::isconcrete($t) {
        if nqp::istype($t, FnType) {
            if $parens {
                '(' ~ $t.Str ~ ')'
            } else {
                $t.Str;
            }
        } elsif nqp::istype($t, TypeVar) {
            $t.Str;
        } else {
            nqp::die('invalid type argument ' ~ describe($t) ~ ' - must not be concrete')
        }
    } else {
        $t.HOW.name($t)
    }
}


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

my $runtime;
my %runtime-fns-types := {};
my %op-types := hash(
    :concat(FnType.new(str, FnType.new(str, str))),
    :escape(FnType.new(str, str)),
);

my sub mkRCall(str $fnName, *@args) {
    nqp::die("invalid runtime fn name $fnName")
        unless nqp::index($fnName, '&') == 0;
    #nqp::die("no such runtime fn: $fnName")
    #    unless nqp::existskey(%runtime-fns-types, $fnName);
    mkCall($fnName, |@args);
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
            if $current.returns =:= str {
                @compressed.push($current);
            } else {
                @compressed.push(mkForce($current));
            }
            $current := $_;
        }
    }
    @compressed.push(mkForce($current));

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
        my @vars := [];
        my $i := 0;
        for $paramNames {
            my $var  := lexVar($_);         #$var.returns(@paramTypes[$i]);
            my $decl := mkDeclP($var);      #$decl.returns(@paramTypes[$i]);
            $body.push($decl);
            @vars.push($var);
            $i++;
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
        #$body.returns($returns);
        %runtime-fns-types{$name} := $returns;
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
        :returns(Type.Fn(Type.Str, Type.Str)), 
    -> $s {
        mkDeclV(lexVar('foo')),
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
    -> $list, $from {
        my $to    := lexVar('to');
        my $out   := lexVar('out');
        my $count := lexVar('count');
        my $n     := lexVar('n');
        
        mkBind(mkDeclV($n),     QAST::Op.new(:op<elems>, $list)),
        mkBind(mkDeclV($count), cloneAndSubst($n)),
        mkBind(mkDeclV($to),    QAST::Op.new(:op<add_i>, $from, $count)),
        mkBind(mkDeclV($out),   mkList()),
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

    mkRFn('&ifTag', <subject tag then else>, 
        #:returns(Type.Fn(NQPMu, Type.Str, NQPMu, NQPMu, NQPMu)), 
        :tagAndId(nqp::null), 
    -> $subject, $tag, $then, $else, $tagAndId {
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
    
    mkRFn('&->#n', <subject tag index>, 
        #:returns(Type.Fn(NQPMu, Type.Str, Type.Int, NQPMu)),
    -> $subject, $tag, $index {
        mkRCall('&ifTag', $subject, $tag,
            QAST::Block.new(:arity(1),
                lexVar('_', :decl<param>),
                mkListLookup($subject, :index($index))
            ),
            QAST::Op.new(:op<null>)
        )
    });
    
    mkRFn('&strOut', <v indent>, 
        #:returns(Type.Fn(NQPMu, Type.Str, Type.Str)), 
    -> $v, $indent {
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
            mkRCall('&strLit', $v),
            mkRCall('&ifTag', 
                $v, 
                'λ',
                QAST::Block.new(:arity(1),
                    mkBind(mkDeclP($id),          mkForce($id)),
                    mkBind(mkDeclV($fvars),       mkRCall('&sublist', $v, 2)),
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
                        #    '  # :tag(', mkRCall('&strLit', mkListLookup($v, :index(0))), ')',
                        #)
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
                                #'(', $dBI, ')',
                                ' = ',
                                QAST::Op.new(:op<if>,
                                    QAST::Op.new(:op<iseq_s>, $name, asNode('self')),
                                    asNode('...'),
                                    mkRCall('&strOut', 
                                        $val,
                                        mkConcat($indent, '#           ')
                                    ),
                                )
                            )
                        )
                    )),
                    $src
                ),
                QAST::Op.new(:op<if>,
                    QAST::Op.new(:op<isint>, $v),
                    $v,
                    mkDelaySimple(QAST::Op.new(:op<reprname>, $v))
                )
            )
        )
    });

    my $tv := Type.Var;

    mkRFn('&delayMemo', <x>, 
        #:returns(Type.Fn(Type.Fn(Type.Void, $tv), Type.Void, $tv)),
        :wasRun(0), :result(nqp::null), 
    -> $x, $wasRun, $result {
        QAST::Block.new(:arity(0),
            QAST::Op.new(:op<if>, $wasRun,
                $result,
                QAST::Stmts.new(
                    mkBind($wasRun, 1),
                    mkBind($result, mkCall($x))
                )
            )
        )
    });
    
    $tv := Type.Var;

    mkRFn('&force', <x>, 
        #:returns(Type.Fn(Type.Fn(Type.Void, $tv), $tv)),
        :foo<bar>,  # prevent it from being inlined
    -> $x, $foo {
        QAST::Op.new(:op<if>,
            QAST::Op.new(:op<isinvokable>, $x),
            mkCall($x),
            $x
        )
    });
    
    mkRFn('&say', <v>, 
        #:returns(Type.Fn(Type.Var, Type.Int)),
    -> $v {
        mkBind($v, mkForce($v)),
        QAST::Op.new(:op<say>,
            QAST::Op.new(:op<if>,
                QAST::Op.new(:op<isstr>, $v),
                $v,
                mkRCall('&strOut', $v, '')
            )
        )
    });
    
    my $tvIn := Type.Var;
    my $tvOut := Type.Var;
    mkRFn('&apply1', <f a1>,
        #:returns(Type.Fn(Type.Fn($tvIn, $tvOut), $tvIn, $tvOut)),
        :result(nqp::null), 
    -> $f, $a1, $result {
        mkBind($f, mkForce($f)),
        mkBind($result, mkCall(
            QAST::Op.new(:op<defor>,
                mkLambda2code($f),
                mkDie('cannot apply ', mkRCall('&strOut', $f, ''), ' to ', mkRCall('&strOut', $a1, ''))
            ),
            $a1
        )),
        mkForce($result),
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

my sub match2location($match) {
    my @lines := nqp::split("\n", nqp::substr($match.orig, 0, $match.from == 0 ?? $match.chars !! $match.from));
    my $lineN := nqp::elems(@lines);
    my $colN  := 1 + nqp::chars(@lines.pop);
    my $file := $*USER_FILE;
    hash(:file($file), :line($lineN), :column($colN), :match($match), :str("$file:$lineN:$colN"));
}

my sub panic($match, *@msg-pieces) {
    if nqp::isconcrete($match) {
        @msg-pieces.push("\n");
        @msg-pieces.push(loc2str(match2location($match)));
    }
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
        self.typecheck($runtime, $top-block);              # <<<<<<<<< TODO

        my $s := $top-block;
        
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

        my $mainTermType;
        $mainTermType := self.typecheck($mainTerm, QAST::Block.new);
        say('MAIN type: ' ~ typeToStr($mainTermType));

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

    sub constrain-eq($t1, $t2) {
        say('>>constraint: ', $t1.Str, ' = ', $t2.Str);
    }
    
    sub make-constraint($t1, $t2, $node) {
        unless ($t1 =:= $t2) || ($t1 =:= Type._) || ($t2 =:= Type._) {
            if $t1.isFnType {
                if $t2.isFnType {
                    make-constraint($t1.in,  $t2.in,  $node);   # TODO: variance
                    make-constraint($t1.out, $t2.out, $node);   # TODO: variance
                } elsif $t2.isTypeVar {
                    constrain-eq($t2, $t1)
                } else {
                    say(dump($node));
                    panic($node.node, 'Type Error: ' ~ $t1.Str ~ ' <> ' ~ $t2.Str);
                }
            } elsif $t1.isTypeVar {
                constrain-eq($t1, $t2)
            } else {
                # t1 is Str, Int, Num, Bool, or Void
                if $t2.isTypeVar {
                    make-constraint($t2, $t1, $node);
                } else {
                    say(dump($node));
                    panic($node.node, 'Type Error: ' ~ $t1.Str ~ ' <> ' ~ $t2.Str);
                }
            }
        }
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

    method typecheck($n, $currentBlock, *@moreBlocks) {
        my $tN := Type.of($n);
        unless $tN {
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
                $tBody := self.typecheck($body, $block, $currentBlock, |@moreBlocks);

                $tBinder.set($binder);
                Type.Fn($tBinder, $tBody).set($n);
            } elsif isApp($n) {
                my $fun := $n[0];
                my $arg := $n[1];
                my $tFun := self.typecheck($fun, $currentBlock, |@moreBlocks);
                my $tArg := self.typecheck($arg, $currentBlock, |@moreBlocks);
                if $tFun.isFnType {
                    make-constraint($tFun.in, $tArg, $n);
                    $n.returns($tFun.out);
                } elsif $tFun.isTypeVar {
                    my $tOut := TypeVar.new;
                    make-constraint($tFun, Type.Fn($tArg, $tOut), $n);
                    $n.returns($tOut);
                } else {
                    say(dump($n));
                    panic($n.node, "Type Error: cannot apply " ~ $tFun.Str, ' to ', $tArg.Str);
                }
            } elsif isRCall($n) {
                my $tRuntimeFn := %runtime-fns-types{$n.name};
                my @tArgs := [];
                @tArgs.push(self.typecheck($_, $currentBlock, |@moreBlocks))
                    for $n.list;

                my $temp := $tRuntimeFn;
                for @tArgs {
                    if $temp.isFnType {
                        make-constraint($temp.in, $_, $n);
                        $temp := $temp.out;
                    } elsif $temp.isTypeVar {
                        my $next := Type.Fn($_, Type.Var);
                        make-constraint($temp, $next, $n);
                        $temp := $next.out;
                    } else {
                        say(dump($n));
                        panic($n.node, 'Type Error: cannot apply runtime fn (', $n.name, ':', $tRuntimeFn.Str, ') to',
                            join(' (', @tArgs, :map(-> $t { $t.Str }), :prefix1st), ')'
                        );
                    }
                }
                $temp.set($n);
            } elsif istype($n, QAST::Stmts, QAST::Stmt) {
                my $tLast := Type.Void;
                $tLast := self.typecheck($_, $currentBlock, |@moreBlocks)
                    for $n.list;
                $tLast.set($n);
            } elsif istype($n, QAST::Block) {
                say('>>>>typechecking Block');
                say(dump($n));
                $n.annotate('positional', []);
                $n.annotate('named',      {});
                $n.annotate('slurpy',     []);
                $n.annotate('optional',   []);
                my $tOut;
                for $n.list {
                    $tOut := self.typecheck($_, $n, $currentBlock, |@moreBlocks);
                }
                if $n.ann('named') || $n.ann('slurpy') || $n.ann('optional') {
                    panic($n.node, 'NYI: typechecking named/slurpy/optional params', ":\n", dump($n, :indent("    ")));
                }
                my @tIns := [];
                for $n.ann('positional') {
                    @tIns.push(Type.of($_));
                    $n.symbol($_.name, :declaration($_));
                }
                @tIns.push(Type.Void)
                    unless @tIns;
                
                say('>>>preparing Block type: ' ~ join(' -> ', @tIns, :map(-> $t { $t.Str })) ~ ' -> ' ~ $tOut.Str);
                my $tBlock := Type.Fn(|@tIns, $tOut);
                $tBlock.set($n);
                say(dump($n));
            } elsif isVar($n) {
                if $n.decl {
                    my $decl := lookup($n.name, $currentBlock)<declaration>;
                    if $decl {
                        panic($n.node, 'redeclaration of ' ~ describe($n) ~ "in \n" ~ dump($currentBlock, :indent('    ')));
                    } else {
                        $currentBlock.symbol($n.name, :declaration($n));
                        Type.Var.set($n);
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
                        my $tVar := Type.of($decl);
                        if $tVar {
                            $tVar.set($n);
                        } else {
                            panic($n.node, 'still untyped: declaration for ' ~ describe($n));
                        }
                    } else {
                        panic($n.node, 'no declaration found for ' ~ describe($n));
                    }
                }
            } elsif isOp($n, 'bind') {
                my $var := $n[0];
                my $val := $n[1];
                my $tVal := self.typecheck($val, $currentBlock, |@moreBlocks);
                my $tVar := self.typecheck($var, $currentBlock, |@moreBlocks);
                # TODO: check if tVar was introduced (if so can ditch the newly introduced Type.Var)
                $tVal.set($n);
                make-constraint($tVar, $tVal, $n);
            } elsif isOp($n, 'list') {
                my @tArgs := [];
                @tArgs.push(self.typecheck($_, $currentBlock, |@moreBlocks))
                    for $n.list;
                Type.Array.set($n);
            } elsif isOp($n) {
                my $tOp := Type.ofOp($n.op);
                if $tOp {
                    my @tArgs := [];
                    @tArgs.push(self.typecheck($_, $currentBlock, |@moreBlocks))
                        for $n.list;

                    my $temp := $tOp;
                    for @tArgs {
                        if $temp.isFnType {
                            make-constraint($temp.in, $_, $n);
                            $temp := $temp.out;
                        } else {
                            say(dump($n));
                            panic($n.node, 'Type Error: cannot apply Op (', $n.op, ':', $tOp.Str, ') to',
                                join(' (', @tArgs, :map(-> $t { $t.Str }), :prefix1st), ')'
                            );
                        }
                    }
                    $temp.set($n);
                } else {
                    say("\n", dump($currentBlock));
                    say("\n", dump($n));
                    nqp::die('Compile Error: dunno type of ' ~ describe($n));
                }
            } else {
                say("\n", dump($n));
                nqp::die('Compile Error: typecheck NYI: ' ~ describe($n));
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
    for [Type.Void, Type.Str, Type.Int, Type.Num, Type.BOOL, Type.Array, Type.Var, Type.Fn(Type.Str, Type.Int), Type.Fn(Type.Void, Type.Var)] {
        say(nqp::sprintf("%15s:", [~$_])
            ~ '  isVoid: '      ~ $_.isVoid
            ~ '  isStrType: '   ~ $_.isStrType
            ~ '  isIntType: '   ~ $_.isIntType
            ~ '  isNumType: '   ~ $_.isNumType
            ~ '  isBoolType: '  ~ $_.isBoolType
            ~ '  isArrayType: ' ~ $_.isArrayType
            ~ '  isTypeVar: '   ~ $_.isTypeVar
            ~ '  isFnType: '    ~ $_.isFnType
        );
    }

    my $F := Type.Fn(Type.Var, Type.Int);
    say('F = ' ~ $F);
    
    my $G := Type.Fn($F, Type.Int);
    say('G = ' ~ $G);
    
    my $H := Type.Fn(Type.Void, $G);
    say('H = ' ~ $H);
    
    my $K := Type.Fn(Type.Void, Type.Int, Type.Str, Type.Var);
    say('K = ' ~ $K);

    for <concat escape isgt_i elems foo> {
        say('Type.ofOp("' ~ $_ ~ '"): ' ~ Type.ofOp($_));
    }

    my $n := lexVar('foo');
    Type.Fn(Type.Void, Type.Int).set($n);
    say(dump($n));


    say(FnType.new(str, int) =:= $F);
    say(FnType.new(int, str) =:= $F);


    #say(isSVal(QAST::Block.new));
    #say(isSVal(QAST::SVal.new));
    #say(isSVal("asdf"));

    say(isOp(QAST::Block.new));
    say(isOp(QAST::Op.new(:op<bind>)));
    say(isOp(QAST::Op.new(:op<bind>), "null"));
    say(isOp(QAST::Op.new(:op<bind>), "bind"));
}
