use NQPHLL;

use Util;
use Util::QAST;
use Util::Compiler;


my class NO_VALUE {}

class Type is export {

    method new(*@args, *%adverbs) {
        nqp::die('cannot instantiate class ' ~ howName(self) ~ ' directly');
    }

    my sub initattrs($instance, $class, %attributes) {
        my $cName := howName($class);
        for $class.HOW.attributes($instance, :local) {
            my $name := $_.name;
            my $pre := nqp::substr($name, 0, 2);
            nqp::die('strange attribute name "' ~ nqp::escape($name) ~ "\" in class $cName - must start with " ~ '"$!", "@!", "%!" or "&!"')
                unless ($pre eq '$!') || ($pre eq '@!') || ($pre eq '%!') || ($pre eq '&!');
            my $key  := nqp::substr($name, 2);
            my $v;
            my $t := $_.type;
            if nqp::existskey(%attributes, $key) {
                $v := %attributes{$key};
            } elsif $pre eq '@!' {
                $v := [];
            } elsif $pre eq '%!' {
                $v := {};
            } else {
                nqp::die("no init value for attribute $name in class $cName"
                       ~ ' (got these: ' ~ describe(%attributes) ~ ')'
                );
            }
            try {   # cannot use Util::insist-isa for all: yields strange error re "cannot unbox a type object" - sometimes...
                my $tName;
                if nqp::isnull($t) {
                    my $typeOK := 0;
                    if $pre eq '$!' {
                        $typeOK := 1;
                        $tName := 'an ' ~ howName(NQPMu);
                    } elsif $pre eq '@!' {
                        $typeOK := nqp::islist($v);
                        $tName := 'a list';
                    } elsif $pre eq '%!' {
                        $typeOK := nqp::ishash($v);
                        $tName := 'a hash';
                    } elsif $pre eq '&!' {
                        $typeOK := nqp::isinvokable($v);
                        $tName := 'an invokable object';
                    }
                    nqp::die('')
                        unless $typeOK;
                    nqp::bindattr($instance, $class, $name, $v);
                } else {
                    $tName := 'a ' ~ howName($t);
                    if $t =:= str {
                        nqp::bindattr_s($instance, $class, $name, $v);
                    } elsif $t =:= int {
                        nqp::bindattr_i($instance, $class, $name, $v);
                    } elsif $t =:= num {
                        nqp::bindattr_n($instance, $class, $name, $v);
                    } else {
                        insist-isa($v, $t);
                        nqp::bindattr($instance, $class, $name, $v);
                    }
                }
                CATCH {
                    my $sName := howName($instance);
                    nqp::die("while initializing a $sName instance, attribute $name declared in class $cName must be $tName - got " ~ describe($v));
                }
            }
        }
        
        #my $m := $p.HOW.method_table($p)<_BUILD>;
        #if $m {
        #    #say(howName($subclass) ~ ' / before ' ~ howName($p) ~ '._BUILD: ' ~ describe(%attributes));
        #    nqp::call($m, $instance, |%attributes);
        #    #say(howName($subclass) ~ ' / after ' ~ howName($p) ~ '._BUILD: ' ~ describe(%attributes));
        #}
   }

    my sub create($subclass, *%attributes) {
        my $sName := howName($subclass);
        my $instance := nqp::create($subclass);
        %attributes<str> := $sName
            unless nqp::existskey(%attributes, 'str');

        my @parents := $subclass.HOW.parents($instance);
        my $i := @parents - 1;
        while $i >= 0 {
            my $p := @parents[$i];
            initattrs($instance, $p, %attributes);
            $i--;
        }

        $instance;
    }

    method set($n) {
        insist-isa($n, QAST::Node);
        nqp::die('cannot use method set on class Type; need a Type instance')
            unless nqp::isconcrete(self);
        $n.annotate('ty', self);
    }

    method elems() { 1 }
    method foldl1(&f) {
        self;

        ## in terms of foldl:
        #my $first := 1;
        #foldl(
        #    -> $acc, $t {
        #        if $first {
        #            $first := 0;
        #            $t;
        #        } else {
        #            &f($acc, $t);
        #        }
        #    },
        #    NO_VALUE
        #);
    }

    method foldl(&f, $start) {
        &f($start, self)

        ## in terms of foldl1:
        #my $first := 1;
        #foldl1(-> $acc, $t {
        #    if $first {
        #        $first := 0;
        #        &f(&f($start, $acc), $t);
        #    } else {
        #        &f($acc, $t);
        #    }
        #});
    }
    

    # will be set below (when subclasses are declared)
    my $Void;
    my $DontCare;
    my $Str;
    my $Int;
    my $Num;
    my $Bool;
    my $Array;

    # will be filled below (when subclasses are declared)
    my %type-vars;
    my %fn-types;
    my %sum-types;
    my %cross-types;


    # must put methods before subclasses s.t. they're are inherited
    # however, we need to call the subs defined *after* the subclasses
    method isVoid()         { self =:= $Void        }
    method isDontCare()     { self =:= $DontCare    }

    method isStr()          { self =:= $Str   }
    method isInt()          { self =:= $Int   }
    method isNum()          { self =:= $Num   }
    method isBool()         { self =:= $Bool  }
    method isArray()        { self =:= $Array }

    method isTypeVar()      { isTypeVar(self)       }
    
    method isFnType()       { isFnType(self)        }
    method isSumType()      { isSumType(self)       }
    method isCrossType()    { isCrossType(self)     }


    method isSimpleType()   { !self.isTypeVar && !self.isCompoundType }
    method isCompoundType() { self.isFnType || self.isSumType || self.isCrossType  }


    has str $!str;

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
    $Int := create(Int);
    method Int() { $Int }

    my class Num is Type {}
    $Num := create(Num);
    method Num() { $Num }


    # the Array type (corresponding to NQP's NQPArray)

    my class Array is Type {}
    $Array := create(Array);
    method Array() { $Array }


    # the Bool type

    my class Bool is Type {}
    $Bool := create(Bool);
    method BOOL() { $Bool } # cannot name it Bool for some reason....


    # the Void type, only to be used in Fn types

    my class Void is Type {}
    $Void := create(Void);
    method Void() { $Void }


    # the DontCare type, to be used for ignored parameters

    my class DontCare is Type {}
    $DontCare := create(DontCare, :str<_>);
    method DontCare() { $DontCare }
    method _() { $DontCare }


    # type variables

    my class Var is Type {
        has int $!id;
        method id()   { $!id     }
        method name() { self.Str }

        method new() {
            my int $id := nqp::elems(%type-vars);
            my str $str := "t$id";
            my $instance := create(Var, :$str, :$id);
            %type-vars{$str} := $instance;
            $instance;
        }
    }

    # compound types (abstract class)

    my class CompoundType is Type {
        has Type $!head;    method head()  { $!head  }
        has Type $!tail;    method tail()  { $!tail  }
        has int  $!elems;   method elems() { $!elems }

        method foldl(&f, $start) {
            my $acc := &f($start, self.head);
            my $tl := self.tail;
            my $myClass := nqp::what(self);
            while nqp::istype($tl, $myClass) {
                $acc := &f($acc, $tl.head);
                $tl := $tl.tail;
            }
            $acc := &f($acc, $tl);
        }
        method foldl1(&f) {
            my $acc := self.head;
            my $tl := self.tail;
            my $myClass := nqp::what(self);
            while nqp::istype($tl, $myClass) {
                $acc := &f($acc, $tl.head);
                $tl := $tl.tail;
            }
            $acc := &f($acc, $tl);
        }
        
    }

    # function types

    my class Fn is CompoundType {
        method new($in, $out) {
            my $str := $in.Str(:outer-parens($in.isFnType || $in.isSumType || $in.isCrossType))
                     ~ ' -> '
                     ~ $out.Str(:outer-parens($out.isSumType));
            my $instance := %fn-types{$str};
            unless $instance {
                my int $elems := 1 + ($out.isFnType ?? $out.elems !! 1);
                $instance := create(self, :$str, :head($in), :tail($out), :$elems);
                %fn-types{$str} := $instance;
            }
            $instance;
        }
        method in()  { self.head }
        method out() { self.tail }
    }


    # sum types

    my class Sum is CompoundType {
        method new(@disjuncts) {
            my $str := join(' + ', @disjuncts, :map(-> $t { $t.Str(:outer-parens($t.isFnType)) }));
            my $instance := %sum-types{$str};
            unless $instance {
                my int $elems := +@disjuncts;
                my $head := @disjuncts.shift;
                my $tail := $elems == 2
                    ?? @disjuncts[0]
                    !! self.new(@disjuncts);
                
                $instance := create(self, :$str, :$head, :$tail, :$elems);
                %sum-types{$str} := $instance;
            }
            $instance;
        }
        
    }

    # cross types (to model NQP's positional args)

    my class Cross is CompoundType {
        method new(@conjuncts) {
            my $str := join(' × ', @conjuncts, :map(-> $t { $t.Str(:outer-parens($t.isFnType || $t.isSumType)) }));
            my $instance := %cross-types{$str};
            unless $instance {
                my int $elems := +@conjuncts;
                my $head := @conjuncts.shift;
                my $tail := $elems == 2
                    ?? @conjuncts[0]
                    !! self.new(@conjuncts);
                
                $instance := create(self, :$str, :$head, :$tail, :$elems);
                %cross-types{$str} := $instance;
            }
            $instance;
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
    
    sub insertion-sort(&cmp, @xs, int $lo = 0, $hi = NO_VALUE) {
        $hi := nqp::elems(@xs) - 1
            if $hi =:= NO_VALUE;
        my int $i := $lo + 1;
        while $i <= $hi {
            my int $k := $i++;
            my int $j := $k--;
            my $x := @xs[$j];
            while ($j > $lo) {
                my $u := @xs[$k];
                if (&cmp($u, $x) > 0) {
                    @xs[$j--] := $u;
                    @xs[$k--] := $x;
                } else {
                    $j := $lo;
                }
            }
        }
        @xs;
    }
    

    method sort(@types) {
        insertion-sort(&lex-cmp, @types);
    }

    my $tThen := Type.Var;
    my $tElse := Type.Var;
    my %op-types := nqp::hash(
        # special (not listed here, but explicitly handled by typecheck)
        #'bind' # how to type the var argument?
        #'list' # due to arbitrary nr of args
        #'hash' # due to arbitrary nr of args (although some constraints, eg even nr of args)
        
        # str
        'concat', Type.Fn(Type.Cross($Str,   $Str    ),     $Str    ),
        'escape', Type.Fn(Type.Cross($Str            ),     $Str    ),
        # int
        'iseq_i', Type.Fn(Type.Cross($Int,   $Int    ),     $Bool   ),
        'isne_i', Type.Fn(Type.Cross($Int,   $Int    ),     $Bool   ),
        'isgt_i', Type.Fn(Type.Cross($Int,   $Int    ),     $Bool   ),
        'isge_i', Type.Fn(Type.Cross($Int,   $Int    ),     $Bool   ),
        'islt_i', Type.Fn(Type.Cross($Int,   $Int    ),     $Bool   ),
        'isle_i', Type.Fn(Type.Cross($Int,   $Int    ),     $Bool   ),
        'neg_i',  Type.Fn(Type.Cross($Int            ),     $Int    ),
        'add_i',  Type.Fn(Type.Cross($Int,   $Int    ),     $Int    ),
        'sub_i',  Type.Fn(Type.Cross($Int,   $Int    ),     $Int    ),
        'mul_i',  Type.Fn(Type.Cross($Int,   $Int    ),     $Int    ),
        'div_i',  Type.Fn(Type.Cross($Int,   $Int    ),     $Int    ),
        'mod_i',  Type.Fn(Type.Cross($Int,   $Int    ),     $Int    ),
        'gcd_i',  Type.Fn(Type.Cross($Int,   $Int    ),     $Int    ),
        'lcm_i',  Type.Fn(Type.Cross($Int,   $Int    ),     $Int    ),
        # list/hash
        'elems',  Type.Fn(Type.Cross($Array          ),     $Int    ),
        'atpos',  Type.Fn(Type.Cross($Array, $Int    ),     Type.Var),
        'push',   Type.Fn(Type.Cross($Array, Type.Var),     $Void   ),
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

    method error(*@pieces, :$at = NO_VALUE, :$panic = &panic) {
        my $match := NQPMu;
        unless $at =:= NO_VALUE {
            insist-isa($at, NQPMatch, QAST::Node);
            if istype($at, QAST::Node) {
                $match := $at.node;
                say(dump($at));
            } else {
                $match := $at;
            }
        }
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
    
    method constrain($t1, $t2, :$at = NO_VALUE, :&onError = NO_VALUE) {
        insist-isa($at, NQPMatch, QAST::Node)
            unless $at =:= NO_VALUE;
        if &onError =:= NO_VALUE {
            &onError := -> *@ps, *%ns { self.error(|@ps, |%ns) }
        } elsif !nqp::isinvokable(&onError) {
            nqp::die('expected an invokable object - got ' ~ describe(&onError));
        }
        
        my $error := 0;
        unless ($t1 =:= $t2) || ($t1 =:= Type._) || ($t2 =:= Type._) {
            if $t1.isSimpleType {
                if $t2.isTypeVar {
                    self.constrain($t2, $t1, :$at);
                } else {
                    $error := 1;
                }
            } elsif $t1.isTypeVar {
                constrain-eq($t1, $t2);
            } else {  # $t1 is compound
                if $t1.isFnType {
                    if $t2.isFnType {
                        self.constrain($t1.in,  $t2.in,  :$at);   # TODO: variance
                        self.constrain($t1.out, $t2.out, :$at);   # TODO: variance
                    } elsif $t2.isTypeVar {
                        constrain-eq($t2, $t1)
                    } else {
                        $error := 1;
                    }
                #} elsif $t1.isSumType {   # TODO
                } elsif $t1.isCrossType {
                    if $t2.isCrossType {
                        if $t1.elems == $t2.elems {
                            self.constrain($t1.head, $t2.tail, :$at);   # TODO: variance
                            self.constrain($t1.head, $t2.tail, :$at);   # TODO: variance
                        } else {
                            $error := 1;
                        }
                    } else {
                        $error := 1;
                    }
                } else {
                    self.error(:$at, 'NYI constraining ', $t1, ' / ', $t2);
                }
            }
        }

        &onError(:$at, $t1, ' <> ', $t2)
            if $error;
    }

}

sub MAIN(*@ARGS) {
}
