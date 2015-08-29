use testing;

use Type;

plan(100);


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


{ # - SumType -----------------------------------------------------------------
    dies_ok( { Type.Sum }, 'Type.Sum with no arg');
    dies_ok( { Type.Sum('foo') }, 'Type.Sum with one arg non-Type');
    dies_ok( { Type.Sum(Type.Void, 42) }, 'Type.Sum with two args, one a non-Type');
    
    my $tv := Type.Var;
    my $tf := Type.Fn(Type.Void, $tv);
    my @types := [Type.Void, Type.Str, Type.Int, Type.BOOL, Type.Array, $tv, $tf];
    
    is(Type.Sum($_), $_, 'Type.Sum with one arg yields that arg (' ~ $_.Str ~ ')')
        for @types;

    is(Type.Sum($_, $_), $_, 'Type.Sum with twice the same arg yields that arg (' ~ $_.Str ~ ')')
        for @types;

    is(Type.Sum($_, $_, $_), $_, 'Type.Sum with thrice the same arg yields that arg (' ~ $_.Str ~ ')')
        for @types;
    
    my $ts := Type.Sum(Type.Int, Type.Str);
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


    is(Type.Fn($ts1, $ts).Str, '(' ~ $ts1.Str ~ ') -> (' ~ $ts.Str ~ ')',
        'Sum type inside a Fn type is always surrounded by parens (left)');

    is(Type.Fn($ts, $ts1).Str, '(' ~ $ts.Str ~ ') -> (' ~ $ts1.Str ~ ')',
        'Sum type inside a Fn type is always surrounded by parens (right)');
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
