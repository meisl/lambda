use NQPHLL;

use Util;
use Util::QAST;
use Util::Compiler;


my class NO_VALUE {}

class Type is export {

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
        has int $!id;
        has str $!name;
        method new() {
            my int $id := nqp::elems(%type-vars);
            my str $name := "t$id";
            my $instance := nqp::create(self);
            nqp::bindattr_i($instance, self, '$!id', $id);
            nqp::bindattr_s($instance, self, '$!name', $name);
            %type-vars{$name} := $instance;
            $instance;
        }
        method Str() { $!name }
        method id()  { $!id   }
    }
    method Var() { Var.new }


    # function types

    my %fn-types := {};
    my class Fn is Type {
        has Type $!in;
        has Type $!out;
        has str  $!str;
        method new($in, $out) {
            Type.insist-isValid($in, $out);
            my $str := ($in.isFnType || $in.isSumType ?? '(' ~ $in.Str ~')' !! $in.Str)
                     ~ ' -> '
                     ~ ($out.isSumType ?? '(' ~ $out.Str ~')' !! $out.Str);
            my $instance := %fn-types{$str};
            unless $instance {
                $instance := nqp::create(self);
                nqp::bindattr($instance, self, '$!in',  $in);
                nqp::bindattr($instance, self, '$!out', $out);
                nqp::bindattr_s($instance, self, '$!str', $str);
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
        has Type $!head;
        has Type $!tail;
        has str  $!str;
        method new(@disjuncts) {
            my $str := join(' + ', @disjuncts, :map(-> $t { $t.isFnType ?? '(' ~ $t.Str ~ ')' !! $t.Str }));
            my $instance := %sum-types{$str};
            unless $instance {
                $instance := nqp::create(self);
                my $head := @disjuncts.shift;
                my $tail := +@disjuncts == 1
                    ?? @disjuncts[0]
                    !! self.new(@disjuncts);
                
                nqp::bindattr(  $instance, self, '$!head', $head);
                nqp::bindattr(  $instance, self, '$!tail', $tail);
                nqp::bindattr_s($instance, self, '$!str',  $str);
                %sum-types{$str} := $instance;
            }
            $instance;
        }
        method head() { $!head }
        method tail() { $!tail }
        method Str()  { $!str  }
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

    method Sum($t0, *@types) {
        @types.push($t0);
        Type.insist-isValid(|@types);
        
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

    my sub isTypeVar($t)   { nqp::istype($t, Var) }
    my sub isFnType($t)    { nqp::istype($t, Fn)  }
    my sub isSumType($t)   { nqp::istype($t, Sum) }



    method isValid($t) {
        nqp::istype($t, Type) && nqp::isconcrete($t)
    }

    method insist-isValid(*@types) {
        nqp::die('expected a valid Type - got ' ~ describe($_))
            unless Type.isValid($_)
                for @types;
    }

    my %type-lexorder := nqp::hash(
        nqp::how($Void    ).name($Void    ), 0,
        nqp::how($DontCare).name($DontCare), 1,
        nqp::how($Bool    ).name($Bool    ), 2,
        nqp::how($Int     ).name($Int     ), 3,
        nqp::how($Num     ).name($Num     ), 4,
        nqp::how($Str     ).name($Str     ), 5,
        nqp::how($Array   ).name($Array   ), 6,
        nqp::how(Var      ).name(Var      ), 7,
        nqp::how(Fn       ).name(Fn       ), 8,
        nqp::how(Sum      ).name(Sum      ), 9,
    );

    my sub lex-cmp($t1, $t2) {
        if $t1 =:= $t2 {
            0;
        } else {
            my $out := %type-lexorder{nqp::how($t1).name($t1)} - %type-lexorder{nqp::how($t2).name($t2)};
            if $out {
                $out;
            } elsif $t1.isTypeVar {
                $t1.id - $t2.id;
            } elsif $t1.isFnType {
                lex-cmp($t1.in, $t2.in) || lex-cmp($t1.out, $t2.out);
            } elsif $t1.isSumType {
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
        # if:
        'if',     Type.Sum(
                    Type.Fn($Bool, $tThen, $tElse, Type.Sum($tThen, $tElse)),
                    Type.Fn($Bool, $tThen, Type.Sum($tThen, $Bool))
                  ),
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
