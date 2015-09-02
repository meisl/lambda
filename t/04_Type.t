use testing;
use Util;

use Type;

plan(284);


{ # - class methods -----------------------------------------------------------
    #is(Type.isVoid, 'asdf');           ?
}


{ # - classifiaction -----------------------------------------------------------
    my sub test-classification($t, *%adverbs) {
        isa_ok($t, Type, |%adverbs, $t.Str(:outer-parens) ~ ' classification');
    }

    test-classification($_, :isCompoundType(0)) for [
        Type.Void,
        Type.DontCare,
        Type.Str,
        Type.Int,
        Type.Num,
        Type.BOOL,
        Type.Array,
        Type.Var,
    ];

    test-classification($_, :isCompoundType(1)) for [
        Type.Fn(Type.Int, Type.Str),
        Type.Sum(Type.Int, Type.Str),
        Type.Cross(Type.Int, Type.Str),
    ];

    test-classification($_, :isSimpleType(1)) for [
        Type.Void,
        Type.DontCare,
        Type.Str,
        Type.Int,
        Type.Num,
        Type.BOOL,
        Type.Array,
    ];

    test-classification($_, :isSimpleType(0)) for [
        Type.Var,
        Type.Fn(Type.Int, Type.Str),
        Type.Sum(Type.Int, Type.Str),
        Type.Cross(Type.Int, Type.Str),
    ];

    test-classification(Type.Void,
        :isVoid(        1),
        :isDontCare(    0),
        :isStr(         0),
        :isInt(         0),
        :isNum(         0),
        :isBool(        0),
        :isArray(       0),
        :isTypeVar(     0),
        :isFnType(      0),
        :isSumType(     0),
        :isCrossType(   0),
    );

    test-classification(Type.DontCare,
        :isVoid(        0),
        :isDontCare(    1),
        :isStr(         0),
        :isInt(         0),
        :isNum(         0),
        :isBool(        0),
        :isArray(       0),
        :isTypeVar(     0),
        :isFnType(      0),
        :isSumType(     0),
        :isCrossType(   0),
    );
    
    test-classification(Type.Str,
        :isVoid(        0),
        :isDontCare(    0),
        :isStr(         1),
        :isInt(         0),
        :isNum(         0),
        :isBool(        0),
        :isArray(       0),
        :isTypeVar(     0),
        :isFnType(      0),
        :isSumType(     0),
        :isCrossType(   0),
    );
    
    test-classification(Type.Int,
        :isVoid(        0),
        :isDontCare(    0),
        :isStr(         0),
        :isInt(         1),
        :isNum(         0),
        :isBool(        0),
        :isArray(       0),
        :isTypeVar(     0),
        :isFnType(      0),
        :isSumType(     0),
        :isCrossType(   0),
    );
    
    test-classification(Type.Num,
        :isVoid(        0),
        :isDontCare(    0),
        :isStr(         0),
        :isInt(         0),
        :isNum(         1),
        :isBool(        0),
        :isArray(       0),
        :isTypeVar(     0),
        :isFnType(      0),
        :isSumType(     0),
        :isCrossType(   0),
    );
    
    test-classification(Type.BOOL,
        :isVoid(        0),
        :isDontCare(    0),
        :isStr(         0),
        :isInt(         0),
        :isNum(         0),
        :isBool(        1),
        :isArray(       0),
        :isTypeVar(     0),
        :isFnType(      0),
        :isSumType(     0),
        :isCrossType(   0),
    );
    
    test-classification(Type.Array,
        :isVoid(        0),
        :isDontCare(    0),
        :isStr(         0),
        :isInt(         0),
        :isNum(         0),
        :isBool(        0),
        :isArray(       1),
        :isTypeVar(     0),
        :isFnType(      0),
        :isSumType(     0),
        :isCrossType(   0),
    );
    
    test-classification(Type.Var,
        :isVoid(        0),
        :isDontCare(    0),
        :isStr(         0),
        :isInt(         0),
        :isNum(         0),
        :isBool(        0),
        :isArray(       0),
        :isTypeVar(     1),
        :isFnType(      0),
        :isSumType(     0),
        :isCrossType(   0),
    );
    
    test-classification(Type.Fn(Type.Int, Type.Str),
        :isVoid(        0),
        :isDontCare(    0),
        :isStr(         0),
        :isInt(         0),
        :isNum(         0),
        :isBool(        0),
        :isArray(       0),
        :isTypeVar(     0),
        :isFnType(      1),
        :isSumType(     0),
        :isCrossType(   0),
    );
    
    test-classification(Type.Sum(Type.Int, Type.Str),
        :isVoid(        0),
        :isDontCare(    0),
        :isStr(         0),
        :isInt(         0),
        :isNum(         0),
        :isBool(        0),
        :isArray(       0),
        :isTypeVar(     0),
        :isFnType(      0),
        :isSumType(     1),
        :isCrossType(   0),
    );
    
    test-classification(Type.Cross(Type.Int, Type.Str),
        :isVoid(        0),
        :isDontCare(    0),
        :isStr(         0),
        :isInt(         0),
        :isNum(         0),
        :isBool(        0),
        :isArray(       0),
        :isTypeVar(     0),
        :isFnType(      0),
        :isSumType(     0),
        :isCrossType(   1),
    );


}


{ # - Void ---------------------------------------------------------------------
    my $t := Type.Void;
    is(Type.Void, $t, 'Type.Void is a singleton');

    my $s := $t.Str;
    is($s, 'Void', '.Str of Type.Void returns a string');
    is($t.Str(:outer-parens), "($s)", 'Type.Void.Str(:outer-parens) returns same string with outer "(", ")" added');
    is($t.Str(:outer-parens(0)), $s, 'Type.Void.Str(:outer-parens(0)) yields no outer parens');
}

{ # - DontCare (aka "_" --------------------------------------------------------
    my $t := Type._;
    is(Type._, $t, 'Type._ is a singleton');

    my $s := $t.Str;
    is($s, '_', '.Str of Type._ returns a string');
    is($t.Str(:outer-parens), "($s)", 'Type._.Str(:outer-parens) returns same string with outer "(", ")" added');
    is($t.Str(:outer-parens(0)), $s, 'Type._.Str(:outer-parens(0)) yields no outer parens');
}

{ # - Str ----------------------------------------------------------------------
    my $t := Type.Str;
    isa_ok($t, Type, 'Type.Str (as a factory method on class Type) returns a Str type instance');
    is(Type.Str, $t, 'Type.Str (as a factory method on class Type) returns same instance on every call');
    my $s := $t.Str;
    is($s, 'Str',  '.Str (as a method on the type instance) returns a string');
    
    is($t.Str(:outer-parens), "($s)", '.Str instance method takes an optional :outer-parens');
    dies_ok({ Type.Str(:outer-parens) }, 'Type.Str factory method does NOT accept :outer-parens');
    is($t.Str(:outer-parens(0)), $s, 'Type.Str.Str(:outer-parens(0)) yields no outer parens');
}

{ # - Var ----------------------------------------------------------------------
    my $t := Type.Var;
    
    my $t2 := Type.Var;
    isa_ok($t2,     Type, 'Type.Var is-a Type (called again)');
    isnt($t2, $t, 'Type.Var returns a different instance on each call');
    
    my $s := $t.Str;
    isa_ok($s, str, 'Type.Var.Str returns a string');
    isnt($t2, $s, 'different Type.Var instances have different .Str reprs');
    
    is($t.Str(:outer-parens), "($s)", 'Type.Var.Str(:outer-parens)');
    is($t.Str(:outer-parens(0)), $s, 'Type.Var.Str(:outer-parens(0)) yields no outer parens');
}

{ # - Fn -----------------------------------------------------------------------
    dies_ok( { Type.Fn },                'Type.Fn with no arg');
    dies_ok( { Type.Fn('foo') },        'Type.Fn with one arg non-Type');
    dies_ok( { Type.Fn(Type.Void) },     'Type.Fn with only one Type arg');
    dies_ok( { Type.Fn(Type.Void, 42) }, 'Type.Fn with two args, one a non-Type');

    my $t := Type.Fn(Type.Void, Type.Void);
    is(Type.Fn(Type.Void, Type.Void), $t, 'Type.Fn returns same instance for same args');

    my $s := $t.Str;
    is($s, Type.Void.Str ~ ' -> ' ~ Type.Void.Str, '.Str of Type.Fn(Type.Void, Type.Void)');
    is($t.Str(:outer-parens), "($s)", '.Str(:outer-parens) of Type.Fn(Type.Void, Type.Void)');
    is($t.Str(:outer-parens(0)), $s, '.Str(:outer-parens(0)) of Type.Fn(Type.Void, Type.Void) yields no outer parens');
}


{ # - Sum ----------------------------------------------------------------------
    dies_ok( { Type.Sum }, 'Type.Sum with no arg');
    dies_ok( { Type.Sum('foo') }, 'Type.Sum with one arg non-Type');
    dies_ok( { Type.Sum(Type.Void, 42) }, 'Type.Sum with two args, one a non-Type');
    
    my $tv := Type.Var;
    my $tf := Type.Fn(Type.Void, $tv);
    my $ts := Type.Sum($tv, $tf);
    my @types := [Type.Void, Type._, Type.BOOL, Type.Int, Type.Num, Type.Str, Type.Array, $tv, $tf, $ts];
    
    is(Type.Sum($_), $_, 'Type.Sum with one arg yields that arg (' ~ $_.Str ~ ')')
        for @types;

    is(Type.Sum($_, $_), $_, 'Type.Sum with twice the same arg yields that arg (' ~ $_.Str ~ ')')
        for @types;

    is(Type.Sum($_, $_, $_), $_, 'Type.Sum with thrice the same arg yields that arg (' ~ $_.Str ~ ')')
        for @types;
    
    my $t := Type.Sum(Type.Int, Type.Str);
    is(Type.Sum(Type.Int, Type.Str), $t, 'Type.Sum with same args returns same instance');
    is(Type.Sum(Type.Str, Type.Int), $t, 'Type.Sum with same args (but in different order) returns same instance');
    
    my $s := $t.Str;
    is($s, Type.Int.Str ~ ' + ' ~ Type.Str.Str, 'Type.Sum(Type.Int, Type.Str).Str');
    is($t.Str(:outer-parens), "($s)", '.Str(:outer-parens) of Type.Sum(Type.Int, Type.Str)');
    is($t.Str(:outer-parens(0)), $s, '.Str(:outer-parens(0)) of Type.Sum(Type.Int, Type.Str) yields no outer parens');

    my $tv1 := Type.Var;
    isnt($tv, $tv1 ,'sanity check: Type.Var returns new instance on each call');

    my $ts1 := Type.Sum($tv, $tv1);
    is($ts1.Str, $tv.Str ~ ' + ' ~ $tv1.Str, '.Str of Type.Sum(' ~ $tv.Str ~ ', ' ~ $tv1.Str ~ ')');
    is(Type.Sum($tv1, $tv), $ts1, :describe(-> $t { $t.Str }),
        'Type.Sum(' ~ $tv1.Str ~ ', ' ~ $tv.Str ~ ') =:= Type.Sum(' ~ $tv.Str ~ ', ' ~ $tv1.Str ~ ')');
    
    my $ts2 := Type.Sum($tf, $tv);
    is($ts2.Str, $tv.Str ~ ' + (' ~ $tf.Str ~ ')', '.Str of Type.Sum(' ~ $tf.Str ~ ', ' ~ $tv.Str ~ ')');
    
    my $ts3 := Type.Sum($tv, $ts1);
    is($ts3.Str, $ts1.Str, 'Type.Sum(' ~ $tv.Str ~ ', ' ~ $ts1.Str ~ ') doesn\'t duplicate disjuncts');
    
    is(Type.Sum($ts1, $tv), $ts1, :describe(-> $t { $t.Str }),
        , 'Type.Sum(' ~ $ts1.Str ~ ', ' ~ $tv.Str ~ ') yields same instance as Type.Sum(' ~ $tv.Str ~ ', ' ~ $ts1.Str ~ ')');

    my $var1 := Type.Var;
    my $var2 := Type.Var;
    my $var3 := Type.Var;
    is(Type.Sum($var3, $var2, $var1).Str, $var1.Str ~ ' + ' ~ $var2.Str ~ ' + ' ~ $var3.Str, '.Str of a Sum with 3 disjuncts');

    is(Type.Fn($ts1, $ts).Str, '(' ~ $ts1.Str ~ ') -> (' ~ $ts.Str ~ ')',
        'Sum type inside a Fn type is always surrounded by parens (left)');

    is(Type.Fn($ts, $ts1).Str, '(' ~ $ts.Str ~ ') -> (' ~ $ts1.Str ~ ')',
        'Sum type inside a Fn type is always surrounded by parens (right)');
}

{ # - Cross --------------------------------------------------------------------
    my $t := Type.Cross;
    isa_ok($t, Type, 'Type.Cross with no arg returns a Type');
    is($t, Type.Void, 'Type.Cross with no arg yields Type.Void');
    is(Type.Cross, $t, 'Type.Cross with same args yields same result (zero args)');
    dies_ok( { Type.Cross('foo') }, 'Type.Cross with one arg non-Type');

    dies_ok( { Type.Sum(Type.Str, 42) }, 'Type.Cross with two args, one a non-Type');
    
    my $tv := Type.Var;
    my $tf := Type.Fn(Type.Void, $tv);
    my $ts := Type.Sum($tv, $tf);
    my @types := [Type.Void, Type._, Type.BOOL, Type.Int, Type.Num, Type.Str, Type.Array, $tv, $tf, $ts];
    
    is(Type.Cross($_), $_, 'Type.Cross with one arg yields that arg (' ~ $_.Str ~ ')')
        for @types;

    lives_ok({ $t := Type.Cross($tv, $tf) }, 'Type.Cross(' ~ $tv ~ ', ' ~ $tf ~ ')');
    isa_ok($t, Type, 'Type.Cross(' ~ $tv ~ ', ' ~ $tf ~ ') is-a Type');
    is(Type.Cross($tv, $tf), $t, :describe(-> $t { $t.Str }), 'Type.Cross with same args yields very same instance');
    
    my $s := $t.Str;
    isa_ok($s, str, '.Str on Cross type returns a string');
    is($t.Str(:outer-parens), "($s)", '.Str(:outer-parens) returns the same string with parentheses added');
    is($t.Str(:outer-parens(0)), $s, '.Str(:outer-parens(0)) yields NO outer parens');

    dies_ok({ Type.Cross($t, $tv) }, 'Cross types must not occur inside another (a)');
    dies_ok({ Type.Cross($tv, $t) }, 'Cross types must not occur inside another (b)');
    
    dies_ok({ Type.Sum($t, $tv) }, 'Cross types must not occur inside a SumType (a)');
    dies_ok({ Type.Sum($tv, $t) }, 'Cross types must not occur inside a SumType (b)');
    
    dies_ok({ Type.Fn($tv, $t) }, 'Cross types must not occur inside a FnType in output position');
    my $sF;
    lives_ok({ $sF := Type.Fn($t, $tv).Str }, 'Cross types may occur inside a FnType in input position');
    
    $s := $t.Str;
    my $sV := $tv.Str;
    is($sF, "($s) -> $sV", 'inner Cross types are shown with parens around them');
}

{ # - (lexical) order of types -------------------------------------------------
    my @types;
    my &map := -> $t { $t.isSumType || $t.isFnType ?? '('~$t.Str~')' !! $t.Str };


    my $var1 := Type.Var;
    my $var2 := Type.Var;
    my $var3 := Type.Var;
    my $num  := Type.Num;
    my $str  := Type.Str;
    my $int  := Type.Int;
    my $bool := Type.BOOL;
    my $_    := Type._;
    my $void := Type.Void;
    my $sum1 := Type.Sum($var2, $var1);
    my $sum2 := Type.Sum($var3, $var1, $var2);
    my $fun1 := Type.Fn($void, $sum2, $var3);
    my $fun2 := Type.Fn($int, $_, $str);
    my $array := Type.Array;
    my $cross1 := Type.Cross($int, $str);
    my $cross2 := Type.Cross($str, $int);

    @types := [$var3, $sum1, $cross1, $array, $num, $_, $cross2, $sum2, $str, $fun1, $bool, $void, $int, $fun2, $var1];
    my $msg := 'Type.sort([' ~ join(', ', @types, :&map) ~ '])';
    is(join(', ', Type.sort(@types),  :&map),
       join(', ', Type.sort([$void, $_, $bool, $int, $num, $str, $array, $var1, $var3, $fun1, $fun2, $sum1, $sum2, $cross1, $cross2]),  :&map),
        $msg);

}


{ # - .head and .tail (of CompoundType s) --------------------------------------
    my $t1 := Type.Str;
    my $t2 := Type.Var;
    my $t3 := Type.Fn($t1, $t2);
    my $t;
    my $s;
    my sub describe($t) { $t.Str }

    $t := Type.Fn($t1, $t2);
    $s := $t.Str(:outer-parens);
    is($t.head, $t1, ".head of $s");
    is($t.tail, $t2, ".tail of $s");

    $t := Type.Fn($t1, $t2, $t3);
    $s := $t.Str(:outer-parens);
    is($t.head, $t1,                ".head of $s", :&describe);
    is($t.tail, Type.Fn($t2, $t3),  ".tail of $s", :&describe);

    $t := Type.Fn($t3, $t2, $t1);
    $s := $t.Str(:outer-parens);
    is($t.head, $t3,                ".head of $s", :&describe);
    is($t.tail, Type.Fn($t2, $t1),  ".tail of $s", :&describe);

    $t := Type.Cross($t1, $t2);
    $s := $t.Str(:outer-parens);
    is($t.head, $t1,                ".head of $s", :&describe);
    is($t.tail, $t2,                ".tail of $s", :&describe);

    $t := Type.Cross($t3, $t2, $t1);
    $s := $t.Str(:outer-parens);
    is($t.head, $t3,                    ".head of $s", :&describe);
    is($t.tail, Type.Cross($t2, $t1),   ".tail of $s", :&describe);

    # Attention: depends on (lexicographic) order on types:
    $t := Type.Sum($t1, $t2);
    $s := $t.Str(:outer-parens);
    is($t.head, $t1,                ".head of $s", :&describe);
    is($t.tail, $t2,                ".tail of $s", :&describe);

    $t := Type.Sum($t1, $t2, $t3);
    $s := $t.Str(:outer-parens);
    is($t.head, $t1,                ".head of $s", :&describe);
    is($t.tail, Type.Sum($t2, $t3), ".tail of $s", :&describe);
}


{ # - QAST::Op types -----------------------------------------------------------
    my @ops := <
        concat escape
        iseq_i isne_i isgt_i isge_i islt_i isle_i    neg_i add_i sub_i mul_i div_i mod_i gcd_i lcm_i
        elems atpos push
        if
    >;
    
    for @ops {
        my $tOp := Type.ofOp($_);
        ok($tOp.isFnType || $tOp.isSumType,
            'Type.ofOp("' ~ $_ ~ '") is-a fn type or a Sum: ' ~ $tOp.Str);
    }

}


{ # - .foldl -------------------------------------------------------------------
    my $t1 := Type.Str;
    my $t2 := Type.Var;
    my $t3 := Type.Fn($t1, $t2);

    my sub recordFoldl(@acc, $t) {
        @acc.push($t);
        @acc;
    }

    for [
        Type.Void, Type._, Type.Str, Type.Int, Type.Num, Type.BOOL, Type.Array, Type.Var,

        #Type.Fn($t1),  # illegal: need at least 2
        Type.Fn($t1, $t2),
        Type.Fn($t1, $t2, $t3),
        Type.Fn($t3, $t2, $t1),
        
        Type.Sum($t1),     # yields non-compound type
        Type.Sum($t1, $t1),# yields non-compound type
        Type.Sum($t1, $t2),
        Type.Sum($t1, $t2, $t3),
        
        Type.Cross($t1),     # yields non-compound type
        Type.Cross($t1, $t2),
        Type.Cross($t1, $t2, $t3),

        #Type.Sum($t1, Type.Cross($t2, $t3)),   # illegal: no Cross inside Sum
        Type.Cross($t1, Type.Sum($t2, $t3)),
        Type.Fn($t1, Type.Sum($t2, $t3)),
        Type.Fn(Type.Sum($t2, $t3), $t1),
        #Type.Fn($t1, Type.Cross($t2, $t3)),    # illegal: Cross only in arg position
        Type.Fn(Type.Cross($t2, $t3), $t1),
        Type.Cross($t1, Type.Fn(Type.Cross($t2, $t3), $t1)),
    ] {
        my $s := $_.Str(:outer-parens);
        my @seen := $_.foldl(&recordFoldl, []);
        if $_.isCompoundType {
            my $c := nqp::what($_);
            my $cs := howName($c);
            my @components := [];
            my $t := $_;
            while nqp::istype($t, $c) {
                @components.push($t.head);
                $t := $t.tail;
            }
            @components.push($t);
            my $n := +@components;
            is(+@seen, $n, ".foldl / $s is compound => should have seen $n components (stopping at non-$cs tail)");
            my $i := 0;
            for @seen {
                my $comp := @components[$i];
                is($_, $comp, ".foldl / $s is compound => should have seen component $i: " ~ $comp.Str);
                $i++;
            }
        } else {
            is(+@seen, 1, ".foldl / $s is not compound => called back once");
            is(@seen[0], $_, ".foldl / $s is not compound => saw just $s");
        }
    }
}

{ # - .elems (non-1 for CompoundType s) ----------------------------------------
    my $t1 := Type.Str;
    my $t2 := Type.Var;
    my $t3 := Type.Fn($t1, $t2);

    my sub countFoldl1($t) {
        my $n := 1;
        $t.foldl1(-> $acc, $s { $n++; });
        $n;
    }

    for [
        Type.Void, Type._, Type.Str, Type.Int, Type.Num, Type.BOOL, Type.Array, Type.Var,

        #Type.Fn($t1),  # illegal: need at least 2
        Type.Fn($t1, $t2),
        Type.Fn($t1, $t2, $t3),
        Type.Fn($t3, $t2, $t1),
        
        Type.Sum($t1),     # yields non-compound type
        Type.Sum($t1, $t1),# yields non-compound type
        Type.Sum($t1, $t2),
        Type.Sum($t1, $t2, $t3),
        
        Type.Cross($t1),     # yields non-compound type
        Type.Cross($t1, $t2),
        Type.Cross($t1, $t2, $t3),

        #Type.Sum($t1, Type.Cross($t2, $t3)),   # illegal: no Cross inside Sum
        Type.Cross($t1, Type.Sum($t2, $t3)),
        Type.Fn($t1, Type.Sum($t2, $t3)),
        Type.Fn(Type.Sum($t2, $t3), $t1),
        #Type.Fn($t1, Type.Cross($t2, $t3)),    # illegal: Cross only in arg position
        Type.Fn(Type.Cross($t2, $t3), $t1),
        Type.Cross($t1, Type.Fn(Type.Cross($t2, $t3), $t1)),
    ] {
        my $n := countFoldl1($_);
        my $s := $_.Str(:outer-parens);
        my $elems := $_.elems;
        is($elems, $n, "$s.elems is as many as seen per .foldl1: $n");
        if $_.isCompoundType {
            ok($elems > 1, "$s is compound => .elems > 1")
                || diag("$s.elems = $elems")
        } else {
            is($elems, 1, "$s is not compound => .elems == 1");
        }
    }
}


{ # - type constraints ---------------------------------------------------------

    my $Str := Type.Str;
    my $Int := Type.Int;
    my $Num := Type.Num;

    dies_ok({ Type.constrain() },                   'Type.constraint with no args');
    dies_ok({ Type.constrain($Int) },               'Type.constraint with one args');
    dies_ok({ Type.constrain($Int, $Int, $Int) },   'Type.constraint with three args');
    
    
    dies_ok({ Type.constrain($Str, $Int) }, 'constraining Int = Str');
}



done();
