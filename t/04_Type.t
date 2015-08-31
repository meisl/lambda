use testing;
use Util;

use Type;

plan(198);

{ # - Type (methods called on the class) --------------------------------------
    #is(Type.isVoid, 'asdf');           ?
}

{ # - Void --------------------------------------------------------------------
    my $t := Type.Void;
    isa_ok($t, Type, 'Type.Void is-a Type');
    is(Type.Void, $t, 'Type.Void is a singleton');

    my $s := $t.Str;
    is($s, 'Void', '.Str of Type.Void returns a string');
    is($t.Str(:outer-parens), "($s)", 'Type.Void.Str(:outer-parens) returns same string with outer "(", ")" added');
    is($t.Str(:outer-parens(0)), $s, 'Type.Void.Str(:outer-parens(0)) yields no outer parens');

    $s := 'Type.Void';
    is($t.isVoid,         1, "$s.isVoid        ");
    is($t.isDontCare,     0, "$s.isDontCare    ");
    is($t.isStr,          0, "$s.isStr         ");
    is($t.isInt,          0, "$s.isInt         ");
    is($t.isNum,          0, "$s.isNum         ");
    is($t.isBool,         0, "$s.isBool        ");
    is($t.isArray,        0, "$s.isArray       ");
    is($t.isTypeVar,      0, "$s.isTypeVar     ");
    is($t.isCompoundType, 0, "$s.isCompoundType");
    is($t.isFnType,       0, "$s.isFnType      ");
    is($t.isSumType,      0, "$s.isSumType     ");
    is($t.isCrossType,    0, "$s.isCrossType   ");
}

{ # - DontCare (aka "_" -------------------------------------------------------
    my $t := Type._;
    isa_ok($t, Type, 'Type._ is-a Type');
    is(Type._, $t, 'Type._ is a singleton');

    my $s := $t.Str;
    is($s, '_', '.Str of Type._ returns a string');
    is($t.Str(:outer-parens), "($s)", 'Type._.Str(:outer-parens) returns same string with outer "(", ")" added');
    is($t.Str(:outer-parens(0)), $s, 'Type._.Str(:outer-parens(0)) yields no outer parens');

    $s := 'Type._';
    is($t.isVoid,         0, "$s.isVoid        ");
    is($t.isDontCare,     1, "$s.isDontCare    ");
    is($t.isStr,          0, "$s.isStr         ");
    is($t.isInt,          0, "$s.isInt         ");
    is($t.isNum,          0, "$s.isNum         ");
    is($t.isBool,         0, "$s.isBool        ");
    is($t.isArray,        0, "$s.isArray       ");
    is($t.isTypeVar,      0, "$s.isTypeVar     ");
    is($t.isCompoundType, 0, "$s.isCompoundType");
    is($t.isFnType,       0, "$s.isFnType      ");
    is($t.isSumType,      0, "$s.isSumType     ");
    is($t.isCrossType,    0, "$s.isCrossType   ");
}

{ # - Str ---------------------------------------------------------------------
    my $t := Type.Str;
    isa_ok($t, Type, 'Type.Str (as a factory method on class Type) returns a Str type instance');
    is(Type.Str, $t, 'Type.Str (as a factory method on class Type) returns same instance on every call');
    my $s := $t.Str;
    is($s, 'Str',  '.Str (as a method on the type instance) returns a string');
    
    is($t.Str(:outer-parens), "($s)", '.Str instance method takes an optional :outer-parens');
    dies_ok({ Type.Str(:outer-parens) }, 'Type.Str factory method does NOT accept :outer-parens');
    is($t.Str(:outer-parens(0)), $s, 'Type.Str.Str(:outer-parens(0)) yields no outer parens');

    $s := 'Type.Str';
    is($t.isVoid,         0, "$s.isVoid        ");
    is($t.isDontCare,     0, "$s.isDontCare    ");
    is($t.isStr,          1, "$s.isStr         ");
    is($t.isInt,          0, "$s.isInt         ");
    is($t.isNum,          0, "$s.isNum         ");
    is($t.isBool,         0, "$s.isBool        ");
    is($t.isArray,        0, "$s.isArray       ");
    is($t.isTypeVar,      0, "$s.isTypeVar     ");
    is($t.isCompoundType, 0, "$s.isCompoundType");
    is($t.isFnType,       0, "$s.isFnType      ");
    is($t.isSumType,      0, "$s.isSumType     ");
    is($t.isCrossType,    0, "$s.isCrossType   ");
}

{ # - Var ---------------------------------------------------------------------
    my $t := Type.Var;
    isa_ok($t,     Type, 'Type.Var is-a Type');
    
    my $t2 := Type.Var;
    isa_ok($t2,     Type, 'Type.Var is-a Type (called again)');
    isnt($t2, $t, 'Type.Var returns a different instance on each call');
    
    my $s := $t.Str;
    isa_ok($s, str, 'Type.Var.Str returns a string');
    isnt($t2, $s, 'different Type.Var instances have different .Str reprs');
    
    is($t.Str(:outer-parens), "($s)", 'Type.Var.Str(:outer-parens)');
    is($t.Str(:outer-parens(0)), $s, 'Type.Var.Str(:outer-parens(0)) yields no outer parens');

    $s := 'Type.Var';
    is($t.isVoid,         0, "$s.isVoid        ");
    is($t.isDontCare,     0, "$s.isDontCare    ");
    is($t.isStr,          0, "$s.isStr         ");
    is($t.isInt,          0, "$s.isInt         ");
    is($t.isNum,          0, "$s.isNum         ");
    is($t.isBool,         0, "$s.isBool        ");
    is($t.isArray,        0, "$s.isArray       ");
    is($t.isTypeVar,      1, "$s.isTypeVar     ");
    is($t.isCompoundType, 0, "$s.isCompoundType");
    is($t.isFnType,       0, "$s.isFnType      ");
    is($t.isSumType,      0, "$s.isSumType     ");
    is($t.isCrossType,    0, "$s.isCrossType   ");
}

{ # - Fn ----------------------------------------------------------------------
    dies_ok( { Type.Fn },                'Type.Fn with no arg');
    dies_ok( { Type.Fn('foo') },        'Type.Fn with one arg non-Type');
    dies_ok( { Type.Fn(Type.Void) },     'Type.Fn with only one Type arg');
    dies_ok( { Type.Fn(Type.Void, 42) }, 'Type.Fn with two args, one a non-Type');

    my $t := Type.Fn(Type.Void, Type.Void);
    isa_ok($t, Type, 'Type.Fn(...) is-a Type');
    is(Type.Fn(Type.Void, Type.Void), $t, 'Type.Fn returns same instance for same args');

    my $s := $t.Str;
    is($s, Type.Void.Str ~ ' -> ' ~ Type.Void.Str, '.Str of Type.Fn(Type.Void, Type.Void)');
    is($t.Str(:outer-parens), "($s)", '.Str(:outer-parens) of Type.Fn(Type.Void, Type.Void)');
    is($t.Str(:outer-parens(0)), $s, '.Str(:outer-parens(0)) of Type.Fn(Type.Void, Type.Void) yields no outer parens');

    $s := "($s)";
    is($t.isVoid,         0, "$s.isVoid        ");
    is($t.isDontCare,     0, "$s.isDontCare    ");
    is($t.isStr,          0, "$s.isStr         ");
    is($t.isInt,          0, "$s.isInt         ");
    is($t.isNum,          0, "$s.isNum         ");
    is($t.isBool,         0, "$s.isBool        ");
    is($t.isArray,        0, "$s.isArray       ");
    is($t.isTypeVar,      0, "$s.isTypeVar     ");
    is($t.isCompoundType, 1, "$s.isCompoundType");
    is($t.isFnType,       1, "$s.isFnType      ");
    is($t.isSumType,      0, "$s.isSumType     ");
    is($t.isCrossType,    0, "$s.isCrossType   ");
}


{ # - Sum ---------------------------------------------------------------------
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

    $s := "($s)";
    is($t.isVoid,         0, "$s.isVoid        ");
    is($t.isDontCare,     0, "$s.isDontCare    ");
    is($t.isStr,          0, "$s.isStr         ");
    is($t.isInt,          0, "$s.isInt         ");
    is($t.isNum,          0, "$s.isNum         ");
    is($t.isBool,         0, "$s.isBool        ");
    is($t.isArray,        0, "$s.isArray       ");
    is($t.isTypeVar,      0, "$s.isTypeVar     ");
    is($t.isCompoundType, 1, "$s.isCompoundType");
    is($t.isFnType,       0, "$s.isFnType      ");
    is($t.isSumType,      1, "$s.isSumType     ");
    is($t.isCrossType,    0, "$s.isCrossType   ");

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

{ # - Cross -------------------------------------------------------------------
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

    $s := "($s)";
    is($t.isVoid,         0, "$s.isVoid        ");
    is($t.isDontCare,     0, "$s.isDontCare    ");
    is($t.isStr,          0, "$s.isStr         ");
    is($t.isInt,          0, "$s.isInt         ");
    is($t.isNum,          0, "$s.isNum         ");
    is($t.isBool,         0, "$s.isBool        ");
    is($t.isArray,        0, "$s.isArray       ");
    is($t.isTypeVar,      0, "$s.isTypeVar     ");
    is($t.isCompoundType, 1, "$s.isCompoundType");
    is($t.isFnType,       0, "$s.isFnType      ");
    is($t.isSumType,      0, "$s.isSumType     ");
    is($t.isCrossType,    1, "$s.isCrossType   ");

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

{ # - (lexical) order of types ------------------------------------------------
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


{ # - QAST::Op types ----------------------------------------------------------
    my @ops := <
        concat escape
        iseq_i isne_i isgt_i isge_i islt_i isle_i    neg_i add_i sub_i mul_i div_i mod_i gcd_i lcm_i
        elems
    >;
    
    for @ops {
        my $tOp := Type.ofOp($_);
        is(Type.isValid($tOp), 1, 'Type.ofOp("' ~ $_ ~ '") is a valid type')
        && is($tOp.isFnType, 1, 'Type.ofOp("' ~ $_ ~ '") is-a fn type');
    }

    diag('Type.ofOp("if"): ' ~ Type.ofOp('if').Str);
}


{ # - .elems (non-1 for CompoundType s) ---------------------------------------
    is($_.elems, 1, $_.Str(:outer-parens) ~ '.elems')
        for [Type.Void, Type._, Type.Str, Type.Int, Type.Num, Type.BOOL, Type.Array, Type.Var];
    
    my $t1 := Type.Str;
    my $t2 := Type.Var;
    my $t3 := Type.Fn($t1, $t2);
    my $t;

    my sub countFoldl1($t) {
        my $n := 1;
        $t.foldl1(-> $acc, $s { $n++; });
        $n;
    }

    is($_.elems, countFoldl1($_), $_.Str(:outer-parens) ~ '.elems is as many as seen per .foldl1')
        for [
            #Type.Fn($t1),  # illegal: need at least 2
            Type.Fn($t1, $t2),
            Type.Fn($t1, $t2, $t3),
            Type.Fn($t3, $t2, $t1),
            
            #Type.Sum($t1),     # yields non-compound type
            Type.Sum($t1, $t2),
            Type.Sum($t1, $t2, $t3),
            
            #Type.Cross($t1),     # yields non-compound type
            Type.Cross($t1, $t2),
            Type.Cross($t1, $t2, $t3),

            #Type.Sum($t1, Type.Cross($t2, $t3)),   # illegal: no Cross inside Sum
            Type.Cross($t1, Type.Sum($t2, $t3)),
            Type.Fn($t1, Type.Sum($t2, $t3)),
            Type.Fn(Type.Sum($t2, $t3), $t1),
            #Type.Fn($t1, Type.Cross($t2, $t3)),    # illegal: Cross only in arg position
            Type.Fn(Type.Cross($t2, $t3), $t1),

        ]
    ;
}



done();
