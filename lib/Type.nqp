use NQPHLL;

use Util;
use Util::QAST;
use Util::Compiler;


my class NO_VALUE {}

class Type is export {

    method new(*@args, *%adverbs) {
        nqp::die('cannot instantiate class Type');
    }

    has str $!str;

    my sub create($subclass, *%attributes) {
        my $instance := nqp::create($subclass);
        my str $str := %attributes<str> // howName($subclass);
        nqp::deletekey(%attributes, 'str');
        nqp::bindattr_s($instance, Type, '$!str', $str);
        for %attributes {
            my $k := '$!' ~ $_.key;
            my $v := $_.value;
            if nqp::isstr($v) {
                nqp::bindattr_s($instance, $subclass, $k, $v);
            } elsif nqp::isint($v) {
                nqp::bindattr_i($instance, $subclass, $k, $v);
            } elsif nqp::isnum($v) {
                nqp::bindattr_n($instance, $subclass, $k, $v);
            } else {
                nqp::bindattr($instance, $subclass, $k, $v);
            }
        }
        $instance;
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
    method isDontCare()  { isDontCare(self)  }

    method isStrType()   { isStrType(self)   }
    method isIntType()   { isIntType(self)   }
    method isNumType()   { isNumType(self)   }
    method isBoolType()  { isBoolType(self)  }
    method isArrayType() { isArrayType(self) }
    
    method isStr()       { isStr(self)   }
    method isInt()       { isInt(self)   }
    method isNum()       { isNum(self)   }
    method isBool()      { isBool(self)  }
    method isArray()     { isArray(self) }

    method isTypeVar()   { isTypeVar(self)   }
    method isFnType()    { isFnType(self)    }
    method isSumType()   { isSumType(self)   }
    method isCrossType() { isCrossType(self) }


    my $Str;
    method Str(:$outer-parens = NO_VALUE) {
        if nqp::isconcrete(self) {
            $outer-parens
                ?? "($!str)"
                !! $!str;
        } else {
            nqp::die("invalid parameter for factory method Type.Str: :outer-parens = " ~ describe($outer-parens))
                unless $outer-parens =:= NO_VALUE;
            $Str;
        }
    }

    # subclasses of Type ------------------------------------------------------

    # native types (corresponding to NQP's str, int, num)

    my class Str is Type {}
    $Str := create(Str);


    my class Int is Type {}
    my $Int := create(Int);
    method Int() { $Int }


    my class Num is Type {}
    my $Num := create(Num);
    method Num() { $Num }


    # the Array type (corresponding to NQP's NQPArray)

    my class Array is Type {}
    my $Array := create(Array);
    method Array() { $Array }


    # the Bool type

    my class Bool is Type {}
    my $Bool := create(Bool);
    method BOOL() { $Bool } # cannot name it Bool for some reason....


    # the Void type, only to be used in Fn types

    my class Void is Type {}
    my $Void := create(Void);
    method Void() { $Void }


    # the DontCare type, to be used for ignored parameters

    my class DontCare is Type {}
    my $DontCare := create(DontCare, :str<_>);
    method DontCare() { $DontCare }
    method _() { $DontCare }


    # type variables

    my %type-vars := {};
    my class Var is Type {
        has int $!id;
        method new() {
            my int $id := nqp::elems(%type-vars);
            my str $str := "t$id";
            my $instance := create(self, :$str, :$id);
            %type-vars{$str} := $instance;
            $instance;
        }
        method id()   { $!id     }
        method name() { self.Str }
    }


    # function types

    my %fn-types := {};
    my class Fn is Type {
        has Type $!in;
        has Type $!out;
        method new($in, $out) {
            my $str := $in.Str(:outer-parens($in.isFnType || $in.isSumType || $in.isCrossType))
                     ~ ' -> '
                     ~ $out.Str(:outer-parens($out.isSumType));
            my $instance := %fn-types{$str};
            unless $instance {
                $instance := create(self, :$str, :$in, :$out);
                %fn-types{$str} := $instance;
            }
            $instance;
        }
        method in()  { $!in  }
        method out() { $!out }
    }


    # sum types

    my %sum-types := {};
    my class Sum is Type {
        has Type $!head;
        has Type $!tail;
        method new(@disjuncts) {
            my $str := join(' + ', @disjuncts, :map(-> $t { $t.Str(:outer-parens($t.isFnType)) }));
            my $instance := %sum-types{$str};
            unless $instance {
                my $head := @disjuncts.shift;
                my $tail := +@disjuncts == 1
                    ?? @disjuncts[0]
                    !! self.new(@disjuncts);
                
                $instance := create(self, :$str, :$head, :$tail);
                %sum-types{$str} := $instance;
            }
            $instance;
        }
        method head() { $!head }
        method tail() { $!tail }
        method foldl1(&f) {
            my $acc := self.head;
            my $tl := self.tail;
            while $tl.isSumType {
                $acc := &f($acc, $tl.head);
                $tl := $tl.tail;
            }
            $acc := &f($acc, $tl);
        }
        
    }

    # cross types (to model NQP's positional args)

    my %cross-types := {};
    my class Cross is Type {
        has Type $!head;
        has Type $!tail;
        method new(@conjuncts) {
            my $str := join(' × ', @conjuncts, :map(-> $t { $t.Str(:outer-parens($t.isFnType || $t.isSumType)) }));
            my $instance := %cross-types{$str};
            unless $instance {
                my $head := @conjuncts.shift;
                my $tail := +@conjuncts == 1
                    ?? @conjuncts[0]
                    !! self.new(@conjuncts);
                
                $instance := create(self, :$str, :$head, :$tail);
                %cross-types{$str} := $instance;
            }
            $instance;
        }
        method head() { $!head }
        method tail() { $!tail }
        method foldl1(&f) {
            my $acc := self.head;
            my $tl := self.tail;
            while $tl.isCrossType {
                $acc := &f($acc, $tl.head);
                $tl := $tl.tail;
            }
            $acc := &f($acc, $tl);
        }
        
    }

    # - factory methods -------------------------------------------------------
    # Note: don't move around stuff lightly - decl order is of importance!

    method Var() { Var.new }

    method Fn($a, $b, *@more) {
        @more.unshift($b);
        @more.unshift($a);
        my $out := @more.pop;
        while @more {
            my $in := @more.pop;
            Type.insist-isValid($in);
            Type.insist-isValid($out, :except(Cross));
            $out := Fn.new($in, $out);
        }
        $out;
    }

    method Sum($t0, *@types) {
        @types.push($t0);
        Type.insist-isValid(|@types, :except(Cross));
        
        # remove duplicates and flatten SumType s
        my %types := {};
        for @types -> $t {
            if $t.isSumType {
                $t.foldl1(-> $acc, $s { %types{$s.Str} := $s });
            } else {
                %types{$t.Str} := $t;
            }
        };

        if +%types == 1 {
            $t0;
        } else {
            @types := [];
            @types.push($_.value)
                for %types;
            my $out := Sum.new(Type.sort(@types));
            $out;
        }
    }

    method Cross(*@types) {
        Type.insist-isValid(|@types, :except(Cross));
        my $n := +@types;
        if $n == 0 {
            Type.Void;
        } elsif $n == 1 {
            @types[0];
        } else {
            Cross.new(@types);
        }
    }

    # - plumbing --------------------------------------------------------------

    my sub isVoid($t)      { $t =:= Type.Void  }
    my sub isDontCare($t)  { $t =:= Type.DontCare }

    my sub isStrType($t)   { $t =:= Type.Str   }
    my sub isIntType($t)   { $t =:= Type.Int   }
    my sub isNumType($t)   { $t =:= Type.Num   }
    my sub isBoolType($t)  { $t =:= Type.BOOL  }
    my sub isArrayType($t) { $t =:= Type.Array }

    my sub isStr($t)       { $t =:= Type.Str   }
    my sub isInt($t)       { $t =:= Type.Int   }
    my sub isNum($t)       { $t =:= Type.Num   }
    my sub isBool($t)      { $t =:= Type.BOOL  }
    my sub isArray($t)     { $t =:= Type.Array }

    my sub isTypeVar($t)   { nqp::istype($t, Var)   }
    my sub isFnType($t)    { nqp::istype($t, Fn)    }
    my sub isSumType($t)   { nqp::istype($t, Sum)   }
    my sub isCrossType($t) { nqp::istype($t, Cross) }



    method isValid($t) {
        nqp::istype($t, Type) && nqp::isconcrete($t)
    }

    method insist-isValid(*@types, :@except = []) {
        @except := [@except]
            unless nqp::islist(@except);
        for @types -> $_ {
            nqp::die('expected a valid Type - got ' ~ describe($_))
                unless Type.isValid($_);
            nqp::die('expected a Type other than ' ~ join(', ', @except, :map(&howName)) ~ ' - got (' ~ $_.Str ~ ')')
                if +@except && istype($_, |@except);
        }
    }

    my %type-lexorder := nqp::hash(
        howName($Void    ),  0,
        howName($DontCare),  1,
        howName($Bool    ),  2,
        howName($Int     ),  3,
        howName($Num     ),  4,
        howName($Str     ),  5,
        howName($Array   ),  6,
        howName(Var      ),  7,
        howName(Fn       ),  8,
        howName(Sum      ),  9,
        howName(Cross    ), 10,
    );

    my sub lex-cmp($t1, $t2) {
        if $t1 =:= $t2 {
            0;
        } else {
            my $out := %type-lexorder{howName($t1)} - %type-lexorder{howName($t2)};
            if $out {
                $out;
            } elsif $t1.isTypeVar {
                $t1.id - $t2.id;
            } elsif $t1.isFnType {
                lex-cmp($t1.in, $t2.in) || lex-cmp($t1.out, $t2.out);
            } elsif $t1.isSumType {
                lex-cmp($t1.head, $t2.head) || lex-cmp($t1.tail, $t2.tail);
            } elsif $t1.isCrossType {
                lex-cmp($t1.head, $t2.head) || lex-cmp($t1.tail, $t2.tail);
            } else {
                nqp::die("NYI: lex-cmp(" ~ $t1.Str ~ ', ' ~ $t2.Str ~ ')');
            }
        }
    }

    sub swap(int $i, int $k, @xs) {
        my $tmp := @xs[$i];
        @xs[$i] := @xs[$k];
        @xs[$k] := $tmp;
    }
    
    sub insertion-sort(&cmp, @types, int $lo, int $hi) {
        my int $n := +@types;
        my int $i := $lo + 1;
        while $i <= $hi {
            my int $j := $i;
            while ($j > $lo) && (&cmp(@types[$j - 1], @types[$j]) > 0) {
                swap($j, $j - 1, @types);
                $j--;
            }
            $i++;
        }
        @types;
    }
    

    method sort(@types) {
        insertion-sort(&lex-cmp, @types, 0, +@types - 1);
    }

    my $tThen := Type.Var;
    my $tElse := Type.Var;
    my %op-types := nqp::hash(
        # special (not listed here, but explicitly handled by typecheck)
        #'bind' # how to type the var argument?
        #'list' # due to arbitrary nr of args
        #'hash' # due to arbitrary nr of args (although some constraints, eg even nr of args)
        
        # str
        'concat', Type.Fn($Str,   $Str, $Str),
        'escape', Type.Fn($Str,   $Str),
        # int
        'iseq_i', Type.Fn($Int,   $Int,   $Bool),
        'isne_i', Type.Fn($Int,   $Int,   $Bool),
        'isgt_i', Type.Fn($Int,   $Int,   $Bool),
        'isge_i', Type.Fn($Int,   $Int,   $Bool),
        'islt_i', Type.Fn($Int,   $Int,   $Bool),
        'isle_i', Type.Fn($Int,   $Int,   $Bool),
        'neg_i',  Type.Fn($Int,   $Int),
        'add_i',  Type.Fn($Int,   $Int,   $Int),
        'sub_i',  Type.Fn($Int,   $Int,   $Int),
        'mul_i',  Type.Fn($Int,   $Int,   $Int),
        'div_i',  Type.Fn($Int,   $Int,   $Int),
        'mod_i',  Type.Fn($Int,   $Int,   $Int),
        'gcd_i',  Type.Fn($Int,   $Int,   $Int),
        'lcm_i',  Type.Fn($Int,   $Int,   $Int),
        # list/hash
        'elems',  Type.Fn($Array, $Int),
        'atpos',  Type.Fn($Array, $Int,     Type.Var),
        'push',   Type.Fn($Array, Type.Var, $Void),
        # if:
        'if',     #Type.Sum(
                  #  Type.Fn($Bool, $tThen,         Type.Sum($Bool,  $tThen)),
                  #  Type.Fn($Bool, $tThen, $tElse, Type.Sum($tThen, $tElse)),
                  #),
                  
                  ##not really:
                  #Type.Fn($Bool, $tThen, Type.Sum($Bool, $tThen, Type.Fn($tElse, Type.Sum($tThen, $tElse)))),
                  ##Bool -> t0 -> (Bool + t0 + (t1 -> (t0 + t1)))

                  ##proper:(Bool × t0 -> (Bool + t0)) + (Bool × t0 × t1 -> (t0 + t1))
                  Type.Sum(
                      Type.Fn(Type.Cross($Bool, $tThen),         Type.Sum($tThen, $Bool )),
                      Type.Fn(Type.Cross($Bool, $tThen, $tElse), Type.Sum($tThen, $tElse)),
                  ),
                  # 
        #'isinvokable',  Type.Fn(Type.Var, $Bool
        #    # Type.Sum(Type.Fn(Type.Var, Type.Var), Type.Fn($Void, Type.Var))
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

    # Type errors

    method error(*@pieces, :$match = NO_VALUE, :$panic = &panic) {
        insist-isa($match, NQPMatch, NQPMu)
            unless $match =:= NO_VALUE;
        nqp::die('no msg (pieces)')
            unless @pieces;
        my $msg := 'Type Error: ';
        $msg := $msg ~ join('', @pieces, :map(-> $p { self.isValid($p) ?? $p.Str !! $p }));
        
        $panic($match, $msg);
    }


    # Type constraints

    sub constrain-eq($t1, $t2) {
        say('>>Type-constraint: ', $t1.Str, ' = ', $t2.Str);
    }
    
    method constrain($t1, $t2, $node) {
        insist-isa($node, QAST::Node);
        unless ($t1 =:= $t2) || ($t1 =:= Type._) || ($t2 =:= Type._) {
            if $t1.isFnType {
                if $t2.isFnType {
                    self.constrain($t1.in,  $t2.in,  $node);   # TODO: variance
                    self.constrain($t1.out, $t2.out, $node);   # TODO: variance
                } elsif $t2.isTypeVar {
                    constrain-eq($t2, $t1)
                } else {
                    say(dump($node));
                    self.error(:match($node.node), $t1, ' <> ', $t2);
                }
            } elsif $t1.isTypeVar {
                constrain-eq($t1, $t2)
            } else {
                # t1 is Str, Int, Num, Bool, or Void
                if $t2.isTypeVar {
                    self.constrain($t2, $t1, $node);
                } else {
                    say(dump($node));
                    self.error(:match($node.node), $t1, ' <> ', $t2);
                }
            }
        }
    }

}

sub MAIN(*@ARGS) {
    say(Type.Void.Str   ~ ' / ' ~ Type.Void.Str(:outer-parens) );
    say(Type._.Str      ~ ' / ' ~ Type._.Str(:outer-parens)    );
    say(Type.BOOL.Str   ~ ' / ' ~ Type.BOOL.Str(:outer-parens)  );
    say(Type.Str.Str    ~ ' / ' ~ Type.Str.Str(:outer-parens)  );
    say(Type.Int.Str    ~ ' / ' ~ Type.Int.Str(:outer-parens)  );
    say(Type.Num.Str    ~ ' / ' ~ Type.Num.Str(:outer-parens)  );
    say(Type.Array.Str  ~ ' / ' ~ Type.Array.Str(:outer-parens));

    my $tv1 := Type.Var;
    say($tv1.Str    ~ ' / ' ~ $tv1.Str(:outer-parens));

    my $tv2 := Type.Var;
    my $tf1 := Type.Fn($tv1, $tv2);
    say($tf1.Str ~ ' / ' ~ $tf1.Str(:outer-parens));
    
    my $tf2 := Type.Fn($tf1, Type.Var);
    say($tf2.Str ~ ' / ' ~ $tf2.Str(:outer-parens));
    
    my $tf3 := Type.Fn(Type.Var, $tf1);
    say($tf3.Str ~ ' / ' ~ $tf3.Str(:outer-parens));

    my $ts := Type.Sum($tv1, $tv2);
    say($ts.Str ~ ' / ' ~ $ts.Str(:outer-parens));
    
    my $tf4 := Type.Fn($ts, $tf1);
    say($tf4.Str ~ ' / ' ~ $tf4.Str(:outer-parens));
    
    my $tf5 := Type.Fn($tf1, $ts);
    say($tf5.Str ~ ' / ' ~ $tf5.Str(:outer-parens));

    my $tc := Type.Cross($tv1, $tv2);
    say($tc.Str ~ ' / ' ~ $tc.Str(:outer-parens));
    
    my $tf6 := Type.Fn($tc, $tf5);
    say($tf6.Str ~ ' / ' ~ $tf6.Str(:outer-parens));
}
