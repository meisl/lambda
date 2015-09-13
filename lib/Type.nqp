use NQPHLL;

use Util;
use Util::QAST;
use Util::Compiler;


my class NO_VALUE {}

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


my role Listy {

    method foreach(&f) {
        my $acc := &f(self.head);
        my $tl := self.tail;
        my $myClass := nqp::what(self);
        while nqp::istype($tl, $myClass) {
            &f($tl.head);
            $tl := $tl.tail;
        }
        &f($tl);
    }

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

    method vars(%vs = {}) {
        if self.isTypeVar {
            %vs{self.name} := self;
        } elsif self.isCompoundType {
            self.head.vars(%vs);
            self.tail.vars(%vs);
        }
        %vs;
    }

    method subst(%s) {
        if self.isTypeVar {
            %s{self.name} // self;
        } elsif self.isCompoundType {
            my @components := self.foldl(
                -> @acc, $t { @acc.push($t.subst(%s)); @acc; },
                []
            );
            if self.isFnType {
                Type.Fn(|@components);
            } elsif self.isSumType {
                Type.Sum(|@components);
            } elsif self.isCrossType {
                Type.Cross(|@components);
            } else {
                nqp::die('cannot subst in compound type: ' ~ self.Str);
            }
        } else {
            self;
        }
    }

    method with-fresh-vars() {
        my %vars := self.vars;
        if +%vars {
            my %subst := {};
            for %vars {
                %subst{$_.key} := Type.Var;
            }
            self.subst(%subst);
        } else {
            self;
        }
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

        method foreach(&f) {
            my $acc := &f(self.head);
            my $tl := self.tail;
            my $myClass := nqp::what(self);
            while nqp::istype($tl, $myClass) {
                &f($tl.head);
                $tl := $tl.tail;
            }
            &f($tl);
        }

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
        method new($head, $tail) {
            my $str := join(' + ', [$head, $tail], :map(-> $t { $t.Str(:outer-parens($t.isFnType)) }));
            my $instance := %sum-types{$str};
            unless $instance {
                my int $elems := 1 + ($tail.isSumType ?? $tail.elems !! 1);
                $instance := create(self, :$str, :$head, :$tail, :$elems);
                %sum-types{$str} := $instance;
            }
            $instance;
        }
        
    }

    # cross types (to model NQP's positional args)

    my class Cross is CompoundType {
        method new($head, $tail) {
            my $str := join(' × ', [$head, $tail], :map(-> $t { $t.Str(:outer-parens($t.isFnType || $t.isSumType)) }));
            my $instance := %cross-types{$str};
            unless $instance {
                my int $elems := 1 + ($tail.isCrossType ?? $tail.elems !! 1);
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
                $t.foldl(-> $acc, $s { %types{$s.Str} := $s }, NO_VALUE);
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
            Type.sort(@types);
            my $out := @types.pop;
            while @types {
                $out := Sum.new(@types.pop, $out);
            }
            $out;
        }
    }

    method Cross(*@types) {
        Type.insist-isValid(
            |@types,
            :except(Cross, Void), 
            :desc('Type.Cross(' ~ join(', ', @types, :map(-> $t { Type.isValid($t) ?? $t.Str !! describe($t) })) ~ ') - ')
        );
        my $n := +@types;
        if $n == 0 {
            Type.Void;
        } elsif $n == 1 {
            @types[0];
        } else {
            my $out := @types.pop;
            while @types {
                $out := Cross.new(@types.pop, $out);
            }
            $out;
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

    method insist-isValid(*@types, :@except = [], :$desc = NO_VALUE) {
        if $desc =:= NO_VALUE {
            $desc := '';
        }
        @except := [@except]
            unless nqp::islist(@except);
        for @types -> $_ {
            nqp::die($desc ~ 'expected a valid Type - got ' ~ describe($_))
                unless Type.isValid($_);
            nqp::die($desc ~ 'expected a Type other than ' ~ join(', ', @except, :map(&howName)) ~ ' - got (' ~ $_.Str ~ ')')
                if +@except && istype($_, |@except);
        }
    }

    sub foldl(@xs, &f, $acc) {
        $acc := &f($acc, $_)
            for @xs;
        $acc;
    }
    

    my %type-lexorder := foldl([
            $Void,
            $DontCare,
            $Bool,
            $Int,
            $Num,
            $Str,
            $Array,
            Var,
            Fn,
            Sum,
            Cross,
        ],
        -> %acc, $t { %acc{howName($t)} := +%acc; %acc; }, # map howName to index in above array
        nqp::hash() # start with empty hash
    );

    sub lex-cmp($t1, $t2) {
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

    method lex-cmp($t1, $t2) {
        Type.insist-isValid($t1, $t2);
        lex-cmp($t1, $t2);
    }

    method sort(@types) {
        Type.insist-isValid(|@types);
        insertion-sort(&lex-cmp, @types);
    }

    my $v0 := Type.Var;
    my $v1 := Type.Var;
    my %op-types := nqp::hash(
        # special (not listed here, but explicitly handled by typecheck)
        #'bind' # how to type the var argument?
        #'call' # due to arbitrary nr of args (at least one, the callee)
        #'list' # due to arbitrary nr of args
        #'hash' # due to arbitrary nr of args (although some constraints, eg even nr of args)
        
        # die
        'die',      Type.Fn(Type.Cross($Str            ),               $Void   ),
        # str
        'isstr',    Type.Fn(Type.Cross($v0             ),               $Bool   ),
        'iseq_s',   Type.Fn(Type.Cross($Str,   $Str    ),               $Bool   ),
        'chars',    Type.Fn(Type.Cross($Str            ),               $Int    ),
        'chr',      Type.Fn(Type.Cross($Int            ),               $Str    ),
        'concat',   Type.Fn(Type.Cross($Str,   $Str    ),               $Str    ),
        'escape',   Type.Fn(Type.Cross($Str            ),               $Str    ),
        'flip',     Type.Fn(Type.Cross($Str            ),               $Str    ),
        'lc',       Type.Fn(Type.Cross($Str            ),               $Str    ),
        'uc',       Type.Fn(Type.Cross($Str            ),               $Str    ),
        'join',     Type.Fn(Type.Cross($Str,   $Array  ),               $Str    ),
        'radix',    Type.Fn(Type.Cross($Int,   $Str, $Int, $Int),       $Array  ),
        'substr',   Type.Sum(
                        Type.Fn(Type.Cross($Str, $Int),                 $Str    ),
                        Type.Fn(Type.Cross($Str, $Int, $Int),           $Str    ),
                    ),
        'split',    Type.Fn(Type.Cross($Str,   $Str   ),                $Array  ),
        # int
        'iseq_i',   Type.Fn(Type.Cross($Int,   $Int    ),               $Bool   ),
        'isne_i',   Type.Fn(Type.Cross($Int,   $Int    ),               $Bool   ),
        'isgt_i',   Type.Fn(Type.Cross($Int,   $Int    ),               $Bool   ),
        'isge_i',   Type.Fn(Type.Cross($Int,   $Int    ),               $Bool   ),
        'islt_i',   Type.Fn(Type.Cross($Int,   $Int    ),               $Bool   ),
        'isle_i',   Type.Fn(Type.Cross($Int,   $Int    ),               $Bool   ),
        'neg_i',    Type.Fn(Type.Cross($Int            ),               $Int    ),
        'add_i',    Type.Fn(Type.Cross($Int,   $Int    ),               $Int    ),
        'sub_i',    Type.Fn(Type.Cross($Int,   $Int    ),               $Int    ),
        'mul_i',    Type.Fn(Type.Cross($Int,   $Int    ),               $Int    ),
        'div_i',    Type.Fn(Type.Cross($Int,   $Int    ),               $Int    ),
        'mod_i',    Type.Fn(Type.Cross($Int,   $Int    ),               $Int    ),
        'gcd_i',    Type.Fn(Type.Cross($Int,   $Int    ),               $Int    ),
        'lcm_i',    Type.Fn(Type.Cross($Int,   $Int    ),               $Int    ),
        'not_i',    Type.Fn(Type.Cross($Int            ),               $Int    ),
        # list/hash
        'elems',    Type.Fn(Type.Cross($Array          ),               $Int    ),
        'atpos',    Type.Fn(Type.Cross($Array, $Int    ),               $v0     ),
        'push',     Type.Fn(Type.Cross($Array, $v0     ),               $Void   ),
        'say',      Type.Sum(
                        Type.Fn($Str,   $Str),
                        Type.Fn($Int,   $Int),
                        Type.Fn($Num,   $Num),
                        Type.Fn($Bool,  $Bool),
                    ),
        # if:
        'if',       Type.Sum(
                        Type.Fn(Type.Cross(Type.Sum($Bool, $Int), $v0  ),               Type.Sum($v0, $Bool)),
                        Type.Fn(Type.Cross(Type.Sum($Bool, $Int), $v0, $v1),            Type.Sum($v0, $v1  )),
                    ),
        'while',    Type.Sum(
                        Type.Fn(Type.Cross(Type.Sum($Bool, $Int), $v0),                 $Bool),
                        Type.Fn(Type.Cross(Type.Sum($Bool, $Int), $v0, $v1),            $v1),   # the variant with a post block
                    ),
                  # 
        'for',      Type.Sum(
                        Type.Fn(Type.Cross($Array, Type.Fn($v0, $v1)),                  $Bool),
                        Type.Fn(Type.Cross($Array, Type.Fn($v0, $v1), $Int),            $Bool),
                    ),
        'isint',    Type.Sum(
                        Type.Fn(
                            Type.Sum(
                                $Str,
                                $Int,     # <<<< True
                                $Num,
                                $Bool,
                                $Array,
                                Type.Fn($v0, $v1),
                            ),
                            $Bool
                        ),
                    ),
        'islist',   Type.Sum(
                        #Type.Fn($Str,               $Bool),
                        #Type.Fn($Int,               $Bool),
                        #Type.Fn($Num,               $Bool),
                        #Type.Fn($Bool,              $Bool),
                        #Type.Fn($Array,             $Bool), # <<<< True
                        #Type.Fn(Type.Fn($v0, $v1),  $Bool),
                        
                        #Type.Fn(
                        #    Type.Sum(
                        #        $Str,
                        #        $Int,
                        #        $Num,
                        #        $Bool,
                        #        Type.Fn($v0, $v1),
                        #    ),
                        #    $Bool
                        #),
                        #Type.Fn($Array, $Bool), # <<<< True

                        Type.Fn(
                            Type.Sum(
                                $Str,
                                $Int,
                                $Num,
                                $Bool,
                                $Array,     # <<<< True
                                Type.Fn($v0, $v1),
                            ),
                            $Bool
                        ),
                    ),
        'isinvokable',  Type.Sum(
                        #Type.Fn($Str,               $Bool),
                        #Type.Fn($Int,               $Bool),
                        #Type.Fn($Num,               $Bool),
                        #Type.Fn($Bool,              $Bool),
                        #Type.Fn($Array,             $Bool),
                        #Type.Fn(Type.Fn($v0, $v1),  $Bool), # <<<< True
                        
                        #Type.Fn(
                        #    Type.Sum(
                        #        $Str,
                        #        $Int,
                        #        $Num,
                        #        $Bool,
                        #        $Array,
                        #    ),
                        #    $Bool
                        #),
                        #Type.Fn(Type.Fn($v0, $v1), $Bool), # <<<< True

                        Type.Fn(
                            Type.Sum(
                                $Str,
                                $Int,
                                $Num,
                                $Bool,
                                $Array,
                                Type.Fn($v0, $v1),     # <<<< True
                            ),
                            $Bool
                        ),
                    ),
        'reprname', Type.Fn(Type.Cross($v0),               $Str   ),
    );
    
    method ofOp($op) {
        unless nqp::isstr($op) {
            nqp::die('expected a str - got ' ~ describe($op));
        }
        my $out := %op-types{$op};
        if $out {
            $out := $out.with-fresh-vars;
        }
        $out;
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
        my $tc := TypeConstraint.get($t1, $t2);
        #say('>>[intermediary Type-constraint: ', $tc.Str, ']');
        $tc;
    }

    my sub ignore(*@ps, *%ns) {
    }
    
    method constrain($t1, $t2, :$at = NO_VALUE, :&onError = NO_VALUE) {
        insist-isa($at, NQPMatch, QAST::Node)
            unless $at =:= NO_VALUE;
        if &onError =:= NO_VALUE {
            &onError := -> *@ps, *%ns { self.error(|@ps, |%ns) }
        } elsif !nqp::isinvokable(&onError) {
            nqp::die('expected an invokable object - got ' ~ describe(&onError));
        }

        my $out := TypeConstraint.False;
        if ($t1 =:= $t2) || ($t1 =:= Type._) || ($t2 =:= Type._) {
            $out := TypeConstraint.True;
        } else {
            if $t1.isSimpleType {
                if $t2.isTypeVar || $t2.isSumType {
                    $out := self.constrain($t2, $t1, :$at, :&onError);
                }
            } elsif $t1.isTypeVar {
                $out := constrain-eq($t1, $t2);
            } else {  # $t1 is compound
                if $t1.isFnType {
                    if $t2.isFnType {
                        $out := TypeConstraint.And(
                            self.constrain($t1.in,  $t2.in,  :$at, :&onError),   # TODO: variance
                            self.constrain($t1.out, $t2.out, :$at, :&onError),   # TODO: variance
                        );
                    } elsif $t2.isTypeVar || $t2.isSumType {
                        $out := self.constrain($t2, $t1, :$at, :&onError);
                    }
                } elsif $t1.isSumType {
                    if $t2.isSimpleType || $t2.isFnType {
                        $out := $t1.foldl(
                            -> $acc, $t { TypeConstraint.Or($acc, self.constrain($t2, $t, :onError(&ignore))) },
                            TypeConstraint.False
                        );
                    } elsif $t2.isTypeVar {
                        $out := constrain-eq($t2, $t1);
                        # TODO: see if it collapse to True
                    } elsif $t2.isSumType {
                        nqp::die("NYI: Sum / Sum");
                    } else {
                        $out := self.constrain($t2, $t1, :$at, :&onError);
                    }
                } elsif $t1.isCrossType {
                    if $t2.isCrossType && ($t1.elems == $t2.elems) {
                        $out := TypeConstraint.And(
                            self.constrain($t1.head, $t2.head, :$at, :&onError),   # TODO: variance
                            self.constrain($t1.tail, $t2.tail, :$at, :&onError),   # TODO: variance
                        );
                    }
                } else {
                    self.error(:$at, 'NYI constraining ', $t1, ' / ', $t2);
                }
            }
        }
        &onError(:$at, $t1, ' <> ', $t2)
            if $out.isFalse;
        $out;
    }
}

class TypeConstraint is export {

    my $True;
    my $False;

    method isTrue()   { self =:= $True  }
    method isFalse()  { self =:= $False }
    method isAtom()   { self.isTrue || self.isFalse }
    
    method isSimple() { self.isAtom || self.isEq }
    method isEq()     { 0 } # overridden in class EqConstraint
    method isAnd()    { 0 } # overridden in class AndConstraint

    method lhs() { nqp::die('cannot get .lhs of ' ~ self.Str) }
    method rhs() { nqp::die('cannot get .rhs of ' ~ self.Str) }

    method vars(%vs = {}) {
        if self.isAtom {
            # nothing
        } elsif self.isEq {
            self.lhs.vars(%vs);
            self.rhs.vars(%vs);
        } elsif self.isAnd {
            self.head.vars(%vs);
            self.tail.vars(%vs);
        } else {
            nqp::die('NYI: .vars on ' ~ self.Str);
        }
        %vs;
    }

    method subst(%s) {
        my $out;
        if self.isAtom {
            $out := self;   # nothing to substitute
        } elsif self.isEq {
            $out := TypeConstraint.get(
                self.lhs.subst(%s),
                self.rhs.subst(%s)
            );
        } else {
            $out := self.foldl(-> $acc, $c { TypeConstraint.And($acc, $c.subst(%s)) }, $True);
        }
        $out;
    }

    method unify() {
        my @out;
        if self.isTrue {
            @out := [{}];
        } elsif self.isFalse {
            
        } elsif self.isEq {
            my $lhs := self.lhs;
            my $rhs := self.rhs;
            if !$lhs.isTypeVar && $rhs.isTypeVar {
                $lhs := $rhs;
                $rhs := self.lhs;
            }
            if $lhs.isTypeVar {
                unless nqp::existskey($rhs.vars, $lhs.name) {
                    @out := [nqp::hash($lhs.name, $rhs)];
                }
            } else {
                @out := Type.constrain($lhs, $rhs).unify;
            }
        } elsif self.isAnd {
            @out := self.head.unify;
            my $tail := self.tail.subst($_) for @out;
            @out.push($_) for $tail.unify;
        }
        unless @out {
            nqp::die("not unifiable: " ~ self.Str);
        }
        @out;
    }

    my class SimpleConstraint is TypeConstraint {
        method foreach(&f)         { &f(self)         }
        method foldl1( &f)         { self             }
        method foldl(  &f, $start) { &f($start, self) }
    }

    my class Atom is SimpleConstraint {
        method Str()       { 'TypeConstraint.' ~ (self.isTrue ?? 'True' !! 'False') }
    }
    
    $True  := nqp::create(Atom);    method True()  { $True  };
    $False := nqp::create(Atom);    method False() { $False };

    my class EqConstraint is SimpleConstraint {
        has Type $!lhs; method lhs() { $!lhs }
        has Type $!rhs; method rhs() { $!rhs }

        method Str() {
            $!lhs.Str(:outer-parens($!lhs.isCompoundType)) ~ ' = ' ~ $!rhs.Str(:outer-parens($!rhs.isCompoundType));
        }
        method isEq() { 1 }
    }

    my class AndConstraint is TypeConstraint {
        has str             $!str;      method Str()  { $!str  }
        has EqConstraint    $!head;     method head() { $!head }
        has TypeConstraint  $!tail;     method tail() { $!tail }

        method new(@conjuncts) {
            my $str := join('  &  ', @conjuncts, :map(-> $t { $t.Str }));
            my $instance;
            my int $elems := +@conjuncts;
            my $head := @conjuncts.shift;
            my $tail := $elems == 2
                ?? @conjuncts[0]
                !! self.new(@conjuncts);
            
            $instance := nqp::create(self);
            nqp::bindattr_s($instance, self, '$!str',  $str);
            nqp::bindattr(  $instance, self, '$!head', $head);
            nqp::bindattr(  $instance, self, '$!tail', $tail);
            nqp::how(self).mixin($instance, Listy);
            $instance;
        }
        method isAnd() { 1 }
    }

    sub remove-dupes(@constraints, :&lex-cmp!, :$unit!, :$zero!, :$flatten = NO_VALUE) {
        my $n := +@constraints;
        if $n == 0 {
            [$unit];
        } elsif $n == 1 {
            @constraints;
        } else {
            my @out := [];
            my %constraints := {};
            for @constraints {
                if nqp::istype($_, $flatten) {
                    $_.foreach(-> $c { %constraints{$c.Str} := $c });
                } elsif lex-cmp($_, $unit) == 0 {
                    # omit
                } elsif lex-cmp($_, $zero) == 0 {
                    @out := [$zero];    # collapse
                } else {
                    %constraints{$_.Str} := $_;
                }
            }
            unless @out {
                @out.push($_.value)
                    for %constraints;
                if +@out == 0 {
                    @out := [$unit];
                } else {
                    insertion-sort(&lex-cmp, @out);
                }
            }
            @out;
        }
    }

    sub lex-cmp($c1, $c2) {
        if $c1.Str eq $c2.Str {
            0
        } elsif $c1.isTrue {
            -1
        } elsif $c1.isFalse {
            $c2.isTrue
                ?? 1
                !! -1;
        } elsif $c1.isEq {
            if $c2.isAtom {
                1;
            } elsif $c2.isEq {
                my $lhss := Type.lex-cmp($c1.lhs, $c2.lhs);
                if $lhss == 0 {
                    Type.lex-cmp($c1.rhs, $c2.rhs);
                } else {
                    $lhss;
                }
            } else {
                -1;
            }
        } elsif nqp::istype($c1, AndConstraint) {
            if $c2.isSimple {
                1;
            } elsif nqp::istype($c2, AndConstraint) {
                my $heads := lex-cmp($c1.head, $c2.head);
                if $heads == 0 {
                    lex-cmp($c1.tail, $c2.tail);
                } else {
                    $heads;
                }
            } else {
                -1;
            }
        } else {
            nqp::die('NYI: lex-cmp(' ~ $c1.Str ~ ', ' ~ $c2.Str ~ ')');
        }
    }
    
    method sort(@constraints) {
        insertion-sort(&lex-cmp, @constraints);
    }

    method And(*@constraints) {
        my @conjuncts := remove-dupes(@constraints,
            :&lex-cmp,
            :unit($True),
            :zero($False),
            :flatten(AndConstraint),
        );
        if +@conjuncts == 1 {
            @conjuncts[0];
        } else {
            AndConstraint.new(@conjuncts);
        }
    }

    method Or(*@constraints) {
        my @disjuncts := remove-dupes(@constraints,
            :&lex-cmp,
            :unit($False),
            :zero($True),
            :flatten(NO_VALUE),
        );
        if +@disjuncts == 1 {
            @disjuncts[0];
        } else {
            nqp::die('NYI: ' ~ join('   +   ', @disjuncts, :map(-> $d { $d.Str })));
            #OrConstraint.new(@disjuncts);
        }
    }


    method get(Type $lhs, Type $rhs) {
        Type.insist-isValid($lhs);
        Type.insist-isValid($rhs);
        if $lhs =:= $rhs {
            $True;
        } else {
            my $out;
            if $lhs.isTypeVar {
                if $rhs.isTypeVar {
                    if $lhs.id > $rhs.id {
                        $out := TypeConstraint.get($rhs, $lhs);
                    }
                }
            } elsif $rhs.isTypeVar {
                $out := TypeConstraint.get($rhs, $lhs);
            }
            unless $out {
                $out := nqp::create(EqConstraint);
                nqp::bindattr($out, EqConstraint, '$!lhs', $lhs);
                nqp::bindattr($out, EqConstraint, '$!rhs', $rhs);
            }
            $out;
        }
    }

}


sub MAIN(*@ARGS) {
    my $var1 := Type.Var;
    my $var2 := Type.Var;

    my $c1a := TypeConstraint.get($var1, Type.Int);
    say($c1a.Str);

    my $c1b := TypeConstraint.get(Type.Int, $var1);
    say($c1b.Str);

    my $c2 := TypeConstraint.get(Type.Int, Type.Int);
    say($c2.Str);

    my $c3 := TypeConstraint.get($var1, $var2);
    say($c3.Str);

    my $c4 := TypeConstraint.get($var2, $var1);
    say($c4.Str);

    say(TypeConstraint.And($c2, $c3).Str);
    say(TypeConstraint.And($c3, $c4).Str);
    say(TypeConstraint.And($c1a, $c3).Str);
    say(TypeConstraint.And($c3, $c1a).Str);

    say('------------');
    my $t12 := Type.Var;
    my $t13 := Type.Var;
    my $t14 := Type.Var;
    my $f := Type.Fn(Type.Cross(Type.BOOL, Type.Int, Type.Str), $t14);
    my $g := Type.Sum(
        Type.Fn(Type.Cross(Type.BOOL, $t12), Type.Sum(Type.BOOL, $t12)),
        Type.Fn(Type.Cross(Type.BOOL, $t12, $t13), Type.Sum($t12, $t13)),
    );
    $g := Type.ofOp('if');
    my $g1 := $g.with-fresh-vars;
    say('f ::' ~ $f.Str);
    say('g ::' ~ $g.Str  ~ ' / ' ~ $g.head.elems);
    say('g1::' ~ $g1.Str ~ ' / ' ~ $g1.head.elems);
    my $c5 := Type.constrain($f, $g);
    say($c5.Str);
    my $c6 := Type.constrain($f, $g1);
    say($c6.Str);

    say('------------');
    my $c7 := TypeConstraint.And($c5, $c4);
    say($c7.Str);

    
    say('------------');
    say($c7 ~ ' => ' ~ describe($c7.unify));
}
