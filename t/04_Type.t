use testing;
use Util;

use Type;

plan(198);

{ # - Type (methods called on the class) --------------------------------------
    #is(Type.isVoid, 'asdf');           ?
}

{ # - Void --------------------------------------------------------------------
    isa_ok(Type.Void, Type, 'Type.Void is-a Type');
    is(Type.Void, Type.Void, 'Type.Void is a singleton');

    my $s := Type.Void.Str;
    is($s, 'Void', '.Str of Type.Void returns a string');
    is(Type.Void.Str(:outer-parens), "($s)", 'Type.Void.Str(:outer-parens) returns same string with outer "(", ")" added');
    is(Type.Void.Str(:outer-parens(0)), $s, 'Type.Void.Str(:outer-parens(0)) yields no outer parens');

    is(Type.Void.isVoid,      1, 'Type.Void.isVoid     ');
    is(Type.Void.isDontCare,  0, 'Type.Void.isDontCare ');
    is(Type.Void.isStr,       0, 'Type.Void.isStr      ');
    is(Type.Void.isInt,       0, 'Type.Void.isInt      ');
    is(Type.Void.isNum,       0, 'Type.Void.isNum      ');
    is(Type.Void.isBool,      0, 'Type.Void.isBool     ');
    is(Type.Void.isArray,     0, 'Type.Void.isArray    ');
    is(Type.Void.isTypeVar,   0, 'Type.Void.isTypeVar  ');
    is(Type.Void.isFnType,    0, 'Type.Void.isFnType   ');
    is(Type.Void.isSumType,   0, 'Type.Void.isSumType  ');
    is(Type.Void.isCrossType, 0, 'Type.Void.isCrossType');
}

{ # - DontCare (aka "_" -------------------------------------------------------
    isa_ok(Type._, Type, 'Type._ is-a Type');
    is(Type._, Type._, 'Type._ is a singleton');

    my $s := Type._.Str;
    is($s, '_', '.Str of Type._ returns a string');
    is(Type._.Str(:outer-parens), "($s)", 'Type._.Str(:outer-parens) returns same string with outer "(", ")" added');
    is(Type._.Str(:outer-parens(0)), $s, 'Type._.Str(:outer-parens(0)) yields no outer parens');

    is(Type._.isVoid,      0, 'Type._.isVoid     ');
    is(Type._.isDontCare,  1, 'Type._.isDontCare ');
    is(Type._.isStr,       0, 'Type._.isStr      ');
    is(Type._.isInt,       0, 'Type._.isInt      ');
    is(Type._.isNum,       0, 'Type._.isNum      ');
    is(Type._.isBool,      0, 'Type._.isBool     ');
    is(Type._.isArray,     0, 'Type._.isArray    ');
    is(Type._.isTypeVar,   0, 'Type._.isTypeVar  ');
    is(Type._.isFnType,    0, 'Type._.isFnType   ');
    is(Type._.isSumType,   0, 'Type._.isSumType  ');
    is(Type._.isCrossType, 0, 'Type._.isCrossType');
}

{ # - Str ---------------------------------------------------------------------
    isa_ok(Type.Str,     Type, 'Type.Str (as a factory method on class Type) returns a Str type instance');
    my $s := Type.Str.Str;
    is($s, 'Str',  '.Str (as a method on the type instance) returns a string');
    
    is(Type.Str.Str(:outer-parens), "($s)", '.Str instance method takes an optional :outer-parens');
    dies_ok({ Type.Str(:outer-parens) }, 'Type.Str factory method does NOT accept :outer-parens');
    is(Type.Str.Str(:outer-parens(0)), $s, 'Type.Str.Str(:outer-parens(0)) yields no outer parens');

    is(Type.Str.isVoid,      0, 'Type.Str.isVoid     ');
    is(Type.Str.isDontCare,  0, 'Type.Str.isDontCare ');
    is(Type.Str.isStr,       1, 'Type.Str.isStr      ');
    is(Type.Str.isInt,       0, 'Type.Str.isInt      ');
    is(Type.Str.isNum,       0, 'Type.Str.isNum      ');
    is(Type.Str.isBool,      0, 'Type.Str.isBool     ');
    is(Type.Str.isArray,     0, 'Type.Str.isArray    ');
    is(Type.Str.isTypeVar,   0, 'Type.Str.isTypeVar  ');
    is(Type.Str.isFnType,    0, 'Type.Str.isFnType   ');
    is(Type.Str.isSumType,   0, 'Type.Str.isSumType  ');
    is(Type.Str.isCrossType, 0, 'Type.Str.isCrossType');
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

    is($t.isVoid,      0, "Type.Var.isVoid     ");
    is($t.isDontCare,  0, "Type.Var.isDontCare ");
    is($t.isStr,       0, "Type.Var.isStr      ");
    is($t.isInt,       0, "Type.Var.isInt      ");
    is($t.isNum,       0, "Type.Var.isNum      ");
    is($t.isBool,      0, "Type.Var.isBool     ");
    is($t.isArray,     0, "Type.Var.isArray    ");
    is($t.isTypeVar,   1, "Type.Var.isTypeVar  ");
    is($t.isFnType,    0, "Type.Var.isFnType   ");
    is($t.isSumType,   0, "Type.Var.isSumType  ");
    is($t.isCrossType, 0, "Type.Var.isCrossType");
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
    is($tf.Str(:outer-parens), "($tfStr)", '.Str(:outer-parens) of Type.Fn(Type.Void, Type.Void)');
    is($tf.Str(:outer-parens(0)), $tfStr, '.Str(:outer-parens(0)) of Type.Fn(Type.Void, Type.Void) yields no outer parens');

    is($tf.isVoid,      0, "($tfStr).isVoid     ");
    is($tf.isDontCare,  0, "($tfStr).isDontCare ");
    is($tf.isStr,       0, "($tfStr).isStr      ");
    is($tf.isInt,       0, "($tfStr).isInt      ");
    is($tf.isNum,       0, "($tfStr).isNum      ");
    is($tf.isBool,      0, "($tfStr).isBool     ");
    is($tf.isArray,     0, "($tfStr).isArray    ");
    is($tf.isTypeVar,   0, "($tfStr).isTypeVar  ");
    is($tf.isFnType,    1, "($tfStr).isFnType   ");
    is($tf.isSumType,   0, "($tfStr).isSumType  ");
    is($tf.isCrossType, 0, "($tfStr).isCrossType");
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
