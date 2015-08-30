use testing;
use Util;

use Type;

plan(139);


{ # - Void --------------------------------------------------------------------
    isa_ok(Type.Void, Type, 'Type.Void is-a Type');
    is(Type.Void, Type.Void, 'Type.Void is a singleton');

    is(Type.Void.isVoid,      1, 'Type.Void.isVoid');
    is(Type.Void.isStrType,   0, 'Type.Void.isStrType  ');
    is(Type.Void.isIntType,   0, 'Type.Void.isIntType  ');
    is(Type.Void.isNumType,   0, 'Type.Void.isNumType  ');
    is(Type.Void.isBoolType,  0, 'Type.Void.isBoolType ');
    is(Type.Void.isArrayType, 0, 'Type.Void.isArrayType');
    is(Type.Void.isTypeVar,   0, 'Type.Void.isTypeVar  ');
    is(Type.Void.isFnType,    0, 'Type.Void.isFnType   ');
    is(Type.Void.isSumType,   0, 'Type.Void.isSumType  ');
}

{ # - Fn ----------------------------------------------------------------------
    dies_ok( { Type.Fn },                'Type.Fn with no arg');
    dies_ok( { Type.Fn('foo') },        'Type.Fn with one arg non-Type');
    dies_ok( { Type.Fn(Type.Void) },     'Type.Fn with only one Type arg');
    dies_ok( { Type.Fn(Type.Void, 42) }, 'Type.Fn with two args, one a non-Type');

    my $tf := Type.Fn(Type.Void, Type.Void);
    isa_ok($tf, Type, 'Type.Fn(...) is-a Type');

    my $tfStr := $tf.Str;
    is($tfStr, Type.Void.Str ~ ' -> ' ~ Type.Void.Str, '.Str of Type.Fn(Type.Void, Type.Void)');

    is($tf.isVoid,      0, "($tfStr).isVoid     ");
    is($tf.isStrType,   0, "($tfStr).isStrType  ");
    is($tf.isIntType,   0, "($tfStr).isIntType  ");
    is($tf.isNumType,   0, "($tfStr).isNumType  ");
    is($tf.isBoolType,  0, "($tfStr).isBoolType ");
    is($tf.isArrayType, 0, "($tfStr).isArrayType");
    is($tf.isTypeVar,   0, "($tfStr).isTypeVar  ");
    is($tf.isFnType,    1, "($tfStr).isFnType   ");
    is($tf.isSumType,   0, "($tfStr).isSumType  ");

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
    
    $ts := Type.Sum(Type.Int, Type.Str);
    is(Type.Sum(Type.Int, Type.Str), $ts, 'Type.Sum with same args returns same instance');
    is(Type.Sum(Type.Str, Type.Int), $ts, 'Type.Sum with same args (but in different order) returns same instance');
    
    is($ts.Str, Type.Int.Str ~ ' + ' ~ Type.Str.Str, 'Type.Sum(Type.Int, Type.Str).Str');
    
    is($ts.isVoid,      0, 'Type.Sum(Type.Int, Type.Str).isVoid');
    is($ts.isStrType,   0, 'Type.Sum(Type.Int, Type.Str).isStrType');
    is($ts.isIntType,   0, 'Type.Sum(Type.Int, Type.Str).isIntType');
    is($ts.isNumType,   0, 'Type.Sum(Type.Int, Type.Str).isNumType');
    is($ts.isBoolType,  0, 'Type.Sum(Type.Int, Type.Str).isBoolType');
    is($ts.isArrayType, 0, 'Type.Sum(Type.Int, Type.Str).isArrayType');
    is($ts.isTypeVar,   0, 'Type.Sum(Type.Int, Type.Str).isTypeVar');
    is($ts.isFnType,    0, 'Type.Sum(Type.Int, Type.Str).isFnType');
    is($ts.isSumType,   1, 'Type.Sum(Type.Int, Type.Str).isSumType');
    
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
    is(Type.Cross, Type.Void, 'Type.Cross with no arg yields Type.Void');
    dies_ok( { Type.Cross('foo') }, 'Type.Cross with one arg non-Type');

    dies_ok( { Type.Sum(Type.Str, 42) }, 'Type.Cross with two args, one a non-Type');
    
    my $tv := Type.Var;
    my $tf := Type.Fn(Type.Void, $tv);
    my $ts := Type.Sum($tv, $tf);
    my @types := [Type.Void, Type._, Type.BOOL, Type.Int, Type.Num, Type.Str, Type.Array, $tv, $tf, $ts];
    
    is(Type.Cross($_), $_, 'Type.Cross with one arg yields that arg (' ~ $_.Str ~ ')')
        for @types;

    my $tc;
    lives_ok({ $tc := Type.Cross($tv, $tf) }, 'Type.Cross(' ~ $tv ~ ', ' ~ $tf ~ ')');
    isa_ok($tc, Type, 'Type.Cross(' ~ $tv ~ ', ' ~ $tf ~ ') is-a Type');
    is(Type.Cross($tv, $tf), $tc, :describe(-> $t { $t.Str }), 'Type.Cross with same args yields very same instance');
    is($tc.isCrossType, 1, 'Type.Cross(' ~ $tv ~ ', ' ~ $tf ~ ').isCrossType');

    dies_ok({ Type.Cross($tc, $tv) }, 'Cross types must not occur inside another (a)');
    dies_ok({ Type.Cross($tv, $tc) }, 'Cross types must not occur inside another (b)');
    
    dies_ok({ Type.Sum($tc, $tv) }, 'Cross types must not occur inside a SumType (a)');
    dies_ok({ Type.Sum($tv, $tc) }, 'Cross types must not occur inside a SumType (b)');
    
    dies_ok({ Type.Fn($tv, $tc) }, 'Cross types must not occur inside a FnType in output position');
    my $tc2s;
    lives_ok({ $tc2s := Type.Fn($tc, $tv).Str }, 'Cross types may occur inside a FnType in input position');
    my $tcs := $tc.Str;
    my $tvs := $tv.Str;
    is($tc2s, "($tcs) -> $tvs", 'inner Cross types are shown with parens around them');
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

done();
