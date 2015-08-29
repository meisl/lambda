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
        has @!disjuncts;
        has $!str;
        method new(*@disjuncts) {
            my $str := join(' + ', @disjuncts, :map(-> $t { toStr($t, :parens) }));
            my $instance := %sum-types{$str};
            unless $instance {
                $instance := nqp::create(self);
                nqp::bindattr($instance, self, '@!disjuncts', @disjuncts);
                nqp::bindattr($instance, self, '$!str',   $str);
                %sum-types{$str} := $instance;
            }
            $instance;
        }
        method Str() { $!str }
    }

    method Sum($t0, *@types) {
        @types.push($t0);
        Type.insist-isValid(|@types);
        
        # remove duplicates and flatten SumType s
        my %types := {};
        for @types -> $t {
            if $t.isSumType {
                %types{$_.Str} := $_
                    for nqp::getattr($t, Sum, '@!disjuncts');
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
            my $out := Sum.new(|@types);
            $out;
        }
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

    method isValid($t) {
        nqp::istype($t, Type) && nqp::isconcrete($t)
    }

    method insist-isValid(*@types) {
        nqp::die('expected a valid Type - got ' ~ describe($_))
            unless Type.isValid($_)
                for @types;
    }

    my sub toStr($t, :$parens) {
        Type.insist-isValid($t);
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

