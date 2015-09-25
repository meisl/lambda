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

    method zipfoldl($t, &f, $start) {
        my $n := self.elems;
        nqp::die('cannot zip ' ~ self.Str ~ ' with ' ~ $t.Str)
            unless $n == $t.elems;
        if $n == 1 {
            &f($start, self, $t);
        } elsif $n == 2 {   # must not zipfoldl into last elem (if that is a different compound type)
            &f(&f($start, self.head, $t.head), self.tail, $t.tail);
        } else {
            self.tail.zipfoldl($t.tail, &f, &f($start, self.head, $t.head));
        }
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
    my $Bot;
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
    method isBot()          { self =:= $Bot         }
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


    # the Bot type, subtype of any other, and empty (ie there is no value of this type)

    my class Bot is Type {
    }
    $Bot := create(Bot);
    method Bot() { $Bot }

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
            $Bot,
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
        'die',      Type.Fn(Type.Cross($Str            ),               $Bot    ),
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
        'stringify',Type.Fn(Type.Cross(Type.Sum($Int, $Num)),           $Str    ),
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
        'predec',   Type.Fn(Type.Cross($Int            ),               $Int    ),
        'preinc',   Type.Fn(Type.Cross($Int            ),               $Int    ),
        'postdec',  Type.Fn(Type.Cross($Int            ),               $Int    ),
        'postinc',  Type.Fn(Type.Cross($Int            ),               $Int    ),
        # list/hash
        'elems',    Type.Fn(Type.Cross($Array          ),               $Int    ),
        'atpos',    Type.Fn(Type.Cross($Array, $Int    ),               $v0     ),
        'push',     Type.Fn(Type.Cross($Array, $v0     ),               $Void   ),
        'say',      Type.Fn(
                        Type.Sum(
                            $Str,
                            $Int,
                            $Num,
                            $Bool,
                            $Array,
                            Type.Fn($Void, $v1),
                        ),
                        $Void
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
        'reprname', Type.Fn(
                        Type.Sum(
                            $Str,
                            $Int,
                            $Num,
                            $Bool,
                            $Array,
                            Type.Fn($v0, $v1),
                        ),
                        $Str
                    ),
    );
    
    method ofOp($op) {
        unless nqp::isstr($op) {
            nqp::die('expected a str - got ' ~ describe($op));
        }
        my $out := %op-types{$op};
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

    my sub ignore(*@ps, *%ns) {
        TypeConstraint.False;
    }

    sub constrain-eq($t1, $t2) {
        my $tc := TypeConstraint.Eq($t1, $t2);
        #say('>>[intermediary Type-constraint: ', $tc.Str, ']');
        $tc;
    }
    
    method constrain($t1, $t2, :$at = NO_VALUE, :&onError = NO_VALUE) {
        insist-isa($at, NQPMatch, QAST::Node)
            unless $at =:= NO_VALUE;
        if &onError =:= NO_VALUE {
            &onError := -> *@ps, *%ns { self.error(|@ps, |%ns) }
        } elsif !nqp::isinvokable(&onError) {
            nqp::die('expected an invokable object - got ' ~ describe(&onError));
        }
        self.insist-isValid($t1, $t2);

        my $out := TypeConstraint.False;
        if ($t1 =:= $t2) || ($t1 =:= Type._) || ($t2 =:= Type._) {
            $out := TypeConstraint.True;
        } else {
            if $t1.isSimpleType {
                if $t2.isTypeVar {
                    $out := self.constrain($t2, $t1, :$at, :&onError);
                }
            } elsif $t1.isTypeVar {
                if $t2.isSumType {
                    $out := TypeConstraint.Eq(
                        $t1,
                        $t2.foldl1(-> $a, $b { $t1 =:= $a ?? $b !! ($t1 =:= $b ?? $a !! Type.Sum($a, $b))})    # kick out t1 from Sum (if any)
                    );
                } else {
                    $out := constrain-eq($t1, $t2);
                }
            } else {  # $t1 is compound
                if $t1.isFnType {
                    if $t2.isFnType {
                        $out := TypeConstraint.And(
                            self.constrain($t1.in,  $t2.in,  :$at, :&onError),
                            self.constrain($t1.out, $t2.out, :$at, :&onError),
                        );
                    } elsif $t2.isTypeVar || $t2.isSumType {
                        $out := self.constrain($t2, $t1, :$at, :&onError);
                    }
                } elsif $t1.isSumType {
                    if $t2.isSimpleType || $t2.isFnType {
                        $out := TypeConstraint.And(
                            self.constrain($t2, $t1.head, :$at, :&onError),
                            self.constrain($t2, $t1.tail, :$at, :&onError),
                        );
                        #    $t1.foldl(
                        #    -> $acc, $t { TypeConstraint.Or($acc, self.constrain($t2, $t, :onError(&ignore))) },
                        #    TypeConstraint.False
                        #);
                        #CATCH {
                        #    say('NYI: ' ~ $t1.Str ~ ' = ' ~ $t2.Str ~ "\n=>");
                        #    nqp::rethrow($_);
                        #}
                    } elsif $t2.isSumType {
                        TypeConstraint.And(
                            self.constrain-sub($t1, $t2, :$at, :&onError),
                            self.constrain-sub($t2, $t1, :$at, :&onError),
                        );
                    } elsif $t2.isTypeVar {
                        $out := constrain-eq($t2, $t1);
                        # TODO: see if it collapse to True
                    #} elsif  {
                    #    self.error(:$at, "NYI: Sum / Sum: ", $t1, '  /  ', $t2);
                    } else {
                        $out := self.constrain($t2, $t1, :$at, :&onError);
                    }
                } elsif $t1.isCrossType {
                    if $t2.isCrossType && ($t1.elems == $t2.elems) {
                        $out := TypeConstraint.And(
                            self.constrain($t1.head, $t2.head, :$at, :&onError),
                            self.constrain($t1.tail, $t2.tail, :$at, :&onError),
                        );
                    }
                } else {
                    self.error(:$at, 'NYI constraining ', $t1, ' / ', $t2);
                }
            }
        }
        $out.isFalse
            ?? &onError(:$at, $t1, ' != ', $t2)
            !! $out;
    }
    
    method constrain-sub($t1, $t2, :$at = NO_VALUE, :&onError = NO_VALUE) {
        insist-isa($at, NQPMatch, QAST::Node)
            unless $at =:= NO_VALUE;
        if &onError =:= NO_VALUE {
            &onError := -> *@ps, *%ns { self.error(|@ps, |%ns) }
        } elsif !nqp::isinvokable(&onError) {
            nqp::die('expected an invokable object - got ' ~ describe(&onError));
        }
        self.insist-isValid($t1, $t2);

        my $out := TypeConstraint.False;
        if ($t1 =:= $t2) {
            $out := TypeConstraint.True;
        } else {
            if $t1.isBot {
                $out := TypeConstraint.True;
            } elsif $t1.isSimpleType {
                if $t2.isSimpleType {
                    #self.error(:$at, "NYI: Simple :< Simple: ", $t1, '  :<  ', $t2);
                } elsif $t2.isTypeVar {
                    $out := TypeConstraint.Sub($t1, $t2);
                } elsif $t2.isFnType || $t2.isCrossType {
                    # FALSE!
                } elsif $t2.isSumType {
                    $out := $t2.foldl(
                        -> $acc, $t {
                            if $acc.isTrue {
                                $acc;
                            } else {
                                my $c := self.constrain-sub($t1, $t, :onError(&ignore));
                                if $c.isTrue {
                                    $c;
                                } elsif $c.isFalse {
                                    $acc;
                                } else {
                                    if $acc.isAtom {
                                        $c
                                    } else {
                                        TypeConstraint.Sub($t1, Type.Sum($acc.rhs, $t));
                                    }
                                }
                                
                            }
                        },
                        TypeConstraint.False
                    );
                    if $out.isSub {
                        say('!!!!!!!!!!!!!!!!!!!!!!!!!!' ~ $out.Str);
                    }
                    
                    #$out := TypeConstraint.Or(
                    #    self.constrain-sub($t1, $t2.head, :onError(&ignore)),
                    #    self.constrain-sub($t1, $t2.tail, :onError(&ignore))
                    #);
                } else {
                    self.error(:$at, "NYI(a): ", $t1, '  :<  ', $t2);
                }
            } elsif $t1.isTypeVar {
                if $t2.isBot {
                    $out := TypeConstraint.Eq($t1, $t2);
                } elsif $t2.isSimpleType || $t2.isTypeVar || $t2.isFnType {
                    $out := TypeConstraint.Sub($t1, $t2);
                } elsif $t2.isFnType {
                    #my $tF := Type.Fn(Type.Var, Type.Var);          # <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<
                    #$out := TypeConstraint.And(
                    #    TypeConstraint.Eq($t1, $tF),
                    #    self.constrain-sub($tF, $t2, :$at, :&onError)
                    #);
                } elsif $t2.isSumType {
                    $out := TypeConstraint.Sub(
                        $t1,
                        $t2.foldl1(-> $a, $b { $t1 =:= $a ?? $b !! ($t1 =:= $b ?? $a !! Type.Sum($a, $b))})    # kick out t1 from Sum (if any)
                    );
                } else {
                    self.error(:$at, "NYI(b): ", $t1, '  :<  ', $t2);
                }
            } elsif $t1.isFnType {
                if $t2.isFnType {
                    $out := TypeConstraint.And(
                        self.constrain-sub($t2.head, $t1.head, :$at, :&onError),   # Fn is contravariant in head
                        self.constrain-sub($t1.tail, $t2.tail, :$at, :&onError),   # Fn is covariant in tail
                    );
                } elsif $t2.isCrossType || $t2.isSimpleType {
                    # FALSE!
                } elsif $t2.isSumType {
                    $out := TypeConstraint.False;
                    my @disjuncts := $t2.foldl(
                        -> $acc, $t {
                            unless $out.isTrue {
                                my $c := self.constrain-sub($t1, $t, :onError(&ignore));
                                if $c.isTrue {
                                    $out:= TypeConstraint.True;
                                } elsif $c.isFalse {
                                    # omit
                                } else {
                                    $acc.push($t);
                                }
                            }
                            $acc;
                        },
                        []
                    );
                    unless $out.isTrue {
                        if +@disjuncts == 0 {
                            $out := TypeConstraint.False;
                        } elsif +@disjuncts == 1 {
                            $out := self.constrain-sub($t1, @disjuncts[0]);
                        } else {
                            $out := TypeConstraint.Sub($t1, Type.Sum(|@disjuncts));
                        }
                        if $out.isSub {
                            say('!!!!!!!!!!!!!!!!!!!!!!!!! ' ~ $t1.Str ~ ' :< ' ~ $t2.Str);
                            say('                       ~> ' ~ $out.Str);
                        }
                        #$out := $t2.foldl(
                        #    -> $acc, $t { TypeConstraint.Or($acc, self.constrain-sub($t1, $t, :onError(&ignore))) },
                        #    TypeConstraint.False
                        #);
                        #CATCH {
                        #    say('NYI(c): ' ~ $t1.Str ~ ' :< ' ~ $t2.Str ~ "\n=>");
                        #    nqp::rethrow($_);
                        #}
                    }
                } elsif $t2.isTypeVar {
                    $out := TypeConstraint.Eq($t2, Type.Sum($t1, Type.Var));
                } else {
                    self.error(:$at, "NYI(d): ", $t1, '  :<  ', $t2);
                }
            } elsif $t1.isSumType {
                if $t2.isTypeVar {
                    $out := TypeConstraint.Sub(
                        $t1.foldl1(-> $a, $b { $t2 =:= $a ?? $b !! ($t2 =:= $b ?? $a !! Type.Sum($a, $b))}),    # kick out t2 from Sum (if any)
                        $t2
                    );
                } elsif $t2.isBot {
                    # FALSE!
                } elsif $t2.isSumType || $t2.isFnType || $t2.isSimpleType {
                    $out := TypeConstraint.And(
                        self.constrain-sub($t1.head, $t2, :$at, :&onError),
                        self.constrain-sub($t1.tail, $t2, :$at, :&onError),
                    );
                } else {
                    self.error(:$at, "NYI(e): ", $t1, '  :<  ', $t2);
                }
            } elsif $t1.isCrossType {
                if $t2.isCrossType && ($t1.elems == $t2.elems) {
                    $out := TypeConstraint.And(
                        self.constrain-sub($t1.head, $t2.head, :$at, :&onError),   # Cross is covariant in head
                        self.constrain-sub($t1.tail, $t2.tail, :$at, :&onError),   # Cross is covariant in tail
                    );
                } elsif $t2.isTypeVar {
                    my $tCross := Type.Cross(|$t1.foldl(-> @acc, $t { @acc.push(Type.Var); @acc; }, []));
                    $out := TypeConstraint.And(
                        self.constrain($t2, $tCross),
                        self.constrain-sub($t1, $tCross)
                    );
                } # else $out := False
            } else {
                self.error(:$at, "NYI(f): ", $t1, '  :<  ', $t2);
            }
        }
        $out.isFalse
            ?? &onError(:$at, $t1, ' !:< ', $t2)
            !! $out;
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
    method isSub()    { 0 } # overridden in class SubConstraint
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

    method subst(%s, :&onError = NO_VALUE) {
        my $out;
        if self.isAtom {
            $out := self;   # nothing to substitute
        } elsif self.isEq {
            $out := Type.constrain(:&onError,
                self.lhs.subst(%s),
                self.rhs.subst(%s)
            );
        } elsif self.isSub {
            $out := Type.constrain-sub(:&onError,
                self.lhs.subst(%s),
                self.rhs.subst(%s)
            );
        } else {
            $out := self.foldl(-> $acc, $c { TypeConstraint.And($acc, $c.subst(%s, :&onError)) }, $True);
        }
        $out;
    }

    method unify() {
        my %out := nqp::null();
        if self.isTrue {
            %out := {};
        } elsif self.isFalse {
            # Boom!
        } elsif self.isEq {
            my $lhs := self.lhs;
            my $rhs := self.rhs;
            if !$lhs.isTypeVar && $rhs.isTypeVar {
                $lhs := $rhs;
                $rhs := self.lhs;
            }
            if $lhs.isTypeVar {
                unless nqp::existskey($rhs.vars, $lhs.name) {   # occur-check, to prevent recursive types
                    %out := nqp::hash($lhs.name, $rhs);
                }
            } else {
                my $simplified := Type.constrain($lhs, $rhs, :onError(-> *@as, *%ns { TypeConstraint.False }));
                unless $simplified.isFalse {
                    %out := $simplified.unify;
                }
            }
        } elsif self.isSub {
            my $lhs := self.lhs;
            my $rhs := self.rhs;
            if $lhs =:= $rhs {
                %out := {};
            } elsif ($lhs.isTypeVar && ($rhs.isSimpleType || $rhs.isTypeVar))    # greedy (but only in isolation, ie if this is the only constraint)
                 || ($rhs.isTypeVar && ($lhs.isSimpleType || $lhs.isTypeVar)) {
                %out := TypeConstraint.Eq($lhs, $rhs).unify;
            } else {
                Type.error('NYI: unify ', self.Str);
            }
        } elsif self.isAnd {
            my $head := self.head;
            if $head.isSub {    # now this And contains only subtype constraints
                my %v2b := self.vars-to-bounds;
                my %bounds := %v2b<bounds>;
                my $rest   := %v2b<rest>;
                if %bounds {
                    say('>>unifying bounds in ' ~ self.Str 
                        #~ ': hash(' ~ join(',  ', %bounds, 
                        #    :map(-> $x {
                        #        ':' ~ $x.key ~ '('
                        #        ~ join(', ', $x.value, :map(-> $y { $y.key ~ ' => ' ~ $y.value.Str }))
                        #        ~ ')';
                        #    })
                        #) ~ ')'
                        ~ ':  bounds(' ~ join('  &  ', %bounds, 
                            :map(-> $x {
                                my $v := $x.key;
                                my $l := $x.value<lower>;
                                my $u := $x.value<upper>;
                                $l ?? $l.Str ~ ' :< ' ~ $v ~ ($u ?? ' :< ' ~ $u.Str !! '') !! $v ~ ' :< ' ~ $u.Str
                            })
                        ) ~ ')'
                    );
                    my $cs := TypeConstraint.True;
                    for %bounds {
                        my $name  := $_.key;
                        my $var   := $_.value<var>;
                        my $upper := $_.value<upper>;
                        my $lower := $_.value<lower>;
                        if $upper {
                            if $lower {
                                $cs := TypeConstraint.And($cs, TypeConstraint.Eq($var, $upper));
                                $rest := TypeConstraint.And($rest, Type.constrain-sub($lower, $upper));
                            } else { # only upper bound
                                #if $upper.isSimpleType {
                                    $cs := TypeConstraint.And($cs, TypeConstraint.Eq($var, $upper));
                                #} else {
                                #    #Type.error('NYI: unify ', $name, ' :< ', $upper.Str);
                                #}
                            }
                        } else {    # only lower bound
                            #if $lower.isSimpleType {
                                $cs := TypeConstraint.And($cs, TypeConstraint.Eq($lower, $var));
                            #} else {
                            #    $cs := TypeConstraint.And($cs, Type.constrain-sub($lower, $var));
                            #}
                        }
                    }
                    Type.error('unify got stuck: ', $cs.Str, ' <= ', self.Str)
                        if $cs.isAtom;
                    say('>>unifying bounds: ' ~ $cs.Str);
                    say('              ...& ' ~ $rest.Str);
                    $cs := TypeConstraint.And($cs, $rest);
                    %out := $cs.unify;
                    say('>>unifying bounds: ' ~ $cs.Str);
                    say('          yielded: ' ~ subst-to-Str(%out));

                } # else { # %bounds empty, ie no "simple" bounds with either lhs a var or rhs a var or both
            } else {
                %out := $head.unify;
                my $tail := self.tail.subst(%out, :onError(-> *@as, *%ns { TypeConstraint.False }));
                if $tail.isFalse {
                    nqp::die("not unifiable: " ~ subst-to-Str(%out) ~ self.tail.Str);
                } else {
                    %out := concat-subst(%out, $tail.unify);
                }
                
            }
        }
        unless nqp::isconcrete(%out) {
            nqp::die("not unifiable: " ~ self.Str);
        }
        %out;
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

    my class SubConstraint is SimpleConstraint {
        has Type $!lhs; method lhs() { $!lhs }
        has Type $!rhs; method rhs() { $!rhs }

        method Str() {
            $!lhs.Str(:outer-parens($!lhs.isCompoundType)) ~ ' :< ' ~ $!rhs.Str(:outer-parens($!rhs.isCompoundType));
        }
        method isSub() { 1 }
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

        method vars-to-bounds() {
            my %bounded-vars := {};
            my $rest := self.foldl(
                -> $acc, $c {
                    my $drop := 0;
                    if $c.isSub {
                        if $c.lhs.isTypeVar {
                            my %entry := %bounded-vars{$c.lhs.name} // (%bounded-vars{$c.lhs.name} := hash(:var($c.lhs)));
                            my $upper := %entry<upper>;
                            if $upper {
                                %entry<upper> := Type.Sum($upper, $c.rhs);
                            } else {
                                %entry<upper> := $c.rhs;
                            }
                            $drop := 1;
                        }
                        if $c.rhs.isTypeVar {
                            my %entry := %bounded-vars{$c.rhs.name} // (%bounded-vars{$c.rhs.name} := hash(:var($c.rhs)));
                            my $lower := %entry<lower>;
                            if $lower {
                                %entry<lower> := Type.Sum($lower, $c.lhs);
                            } else {
                                %entry<lower> := $c.lhs;
                            }
                            $drop := 1;
                        }
                    }
                    if $drop {
                        $acc
                    } else {
                        TypeConstraint.And($acc, $c);
                    }
                },
                TypeConstraint.True
            );
            my %out := nqp::hash(
                'bounds', %bounded-vars,
                'rest', $rest,
            );
            %out;
        }
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
        insist-isa($c1, TypeConstraint);
        insist-isa($c2, TypeConstraint);
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
        } elsif $c1.isSub {
            if $c2.isAtom || $c2.isEq {
                1;
            } elsif $c2.isSub {
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


    method Eq(Type $lhs, Type $rhs) {
        Type.insist-isValid($lhs);
        Type.insist-isValid($rhs);
        if $lhs =:= $rhs {
            $True;
        } else {
            my $out;
            if $lhs.isTypeVar {
                if $rhs.isTypeVar {
                    if $lhs.id > $rhs.id {
                        $out := TypeConstraint.Eq($rhs, $lhs);
                    }
                }
            } elsif $rhs.isTypeVar {
                $out := TypeConstraint.Eq($rhs, $lhs);
            }
            unless $out {
                $out := nqp::create(EqConstraint);
                nqp::bindattr($out, EqConstraint, '$!lhs', $lhs);
                nqp::bindattr($out, EqConstraint, '$!rhs', $rhs);
            }
            $out;
        }
    }

    method Sub(Type $lhs, Type $rhs) {
        Type.insist-isValid($lhs);
        Type.insist-isValid($rhs);
        if $lhs =:= $rhs {
            $True;
        } else {
            my $out := nqp::create(SubConstraint);
            nqp::bindattr($out, SubConstraint, '$!lhs', $lhs);
            nqp::bindattr($out, SubConstraint, '$!rhs', $rhs);
            $out;
        }
    }

}

sub concat-subst(*@ss) {
    if +@ss == 0 {
        {};
    } else {
        my %s1 := @ss.shift;
        for @ss {
            my %s2 := $_;
            my %out := {};
            for %s1 {
                %out{$_.key} := $_.value.subst(%s2);
            }
            for %s2 {
                unless nqp::existskey(%out, $_.key) {
                    %out{$_.key} := $_.value;
                }
            }
            %s1 := %out;
        }
        %s1;
    }
}


sub subst-to-Str(@ss) {
    if nqp::ishash(@ss) {
        @ss := [@ss];
    }
    join('; ', @ss, :map(-> %subst { 
        if nqp::ishash(%subst) {
            '[' ~ join(', ', %subst, :map(-> $_ { $_.key ~ ' » ' ~ $_.value.Str(:outer-parens($_.value.isCompoundType)) })) ~ ']'
        } else {
            describe(%subst);
        }
    }));
}


sub MAIN(*@ARGS) {
    my $var0 := Type.Var;
    my $var1 := Type.Var;
    my $var2 := Type.Var;
    my $var3 := Type.Var;
    my $var4 := Type.Var;
    my $var5 := Type.Var;
    my $var6 := Type.Var;

    my $t69a := Type.Sum($var0, Type.Str, Type.Int);
    my $t69b := Type.Sum(Type.Str, Type.Num, $var0, $var1);
    my $c69 := Type.constrain-sub($t69a, $t69b);    #     t2 + Int + Str :< Num + Str + t2 + t3
    say($t69a ~ ' :< ' ~ $t69b);                    # =>  t2  :< Num + Str + t2 + t3  [~> t2  :< Num + Str + t3]
    say($c69.Str);                                  #   & Int :< Num + Str + t2 + t3  [~> Int :< t2 + t3]
    say(subst-to-Str($c69.unify));                  #   & Str :< Num + Str + t2 + t3  [~> True]
    say('---------');

    my $c74 := TypeConstraint.And(
        Type.constrain($var0, Type.Num),
        Type.constrain($var0, $var1),
        Type.constrain($var1, Type.Int),
        Type.constrain($var1, Type.Str),
    );
    say($c74.Str);
    say(subst-to-Str($c74.unify));
    say('---------');

    my $t1 := Type.Fn($var0, $var1);
    my $t2 := Type.Fn($var5, $var6);
    say($t1.Str ~ ' :< ' ~ $var2.Str ~ '  &  ' ~ $var2.Str ~ ' :< ' ~ $t2.Str);
    my $c99 := TypeConstraint.And(
        Type.constrain-sub($t1, $var2),
        Type.constrain-sub($var2, $t2)
    );
    say($c99.Str);
    my $u99 := $c99.unify;
    say(subst-to-Str($u99));
    say(subst-to-Str(concat-subst($u99)));
    $t1 := $t1.subst($_);
    $t2 := $t2.subst($_);
    say($t1.Str, ', ', $t2.Str);
    say('---------');

    my $c42a := Type.constrain-sub(Type.Sum($var1, $var2), $var1);
    my $c42b := Type.constrain-sub($var1, Type.Sum($var1, $var2));
    my $c42 := TypeConstraint.And($c42a, $c42b);
    say($c42.Str);
    say(subst-to-Str($c42.unify));
    say('---------');

    my $c23 := Type.constrain-sub(                      #     T1 × T1 × T2 × T1 × T3  :<  T1 × T2 × T1 × T3 × Int
        Type.Cross($var1, $var1, $var2, $var1, $var3),         # =>  T1 :< T1  &  T1 :< T2  &  T2 :< T1  &  T1 :< T3  &  T3 :< Int
        Type.Cross($var1, $var2, $var1, $var3, Type.Int)
    );
    say($c23.Str);
    my $u23 := $c23.unify;
    say(subst-to-Str($u23));
    my $u23a := concat-subst($u23);
    say(subst-to-Str($u23a));
    nqp::exit(0);
    

    my $c1a := TypeConstraint.Eq($var1, Type.Int);
    say($c1a.Str);

    my $c1b := TypeConstraint.Eq(Type.Int, $var1);
    say($c1b.Str);

    my $c2 := TypeConstraint.Eq(Type.Int, Type.Int);
    say($c2.Str);

    my $c3 := TypeConstraint.Eq($var1, $var2);
    say($c3.Str);

    my $c4 := TypeConstraint.Eq($var2, $var1);
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
