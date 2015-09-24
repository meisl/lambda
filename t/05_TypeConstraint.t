use testing;
use Util;

use Type;

plan(111);


{ # - class methods -----------------------------------------------------------
}


{ # - classification -----------------------------------------------------------
    my sub test-classification($t, *%adverbs) {
        isa_ok($t, TypeConstraint, |%adverbs, '(' ~ $t.Str ~ ') classification');
    }

    my $True  := TypeConstraint.True;
    my $False := TypeConstraint.False;

    test-classification($_, :isAtom(1), :isSimple(1), :isEq(0), :isAnd(0)) for [
        $True,
        $False,
    ];

    my $eq1 := TypeConstraint.Eq(Type.Var, Type.Str);
    my $eq2 := TypeConstraint.Eq(Type.Var, Type.Sum(Type.Int, Type.Str));
    my $eq3 := TypeConstraint.Eq(Type.Var, Type.Cross(Type.Int, Type.Str));

    test-classification($_, :isAtom(0), :isSimple(1), :isEq(1), :isAnd(0)) for [
        $eq1,
        $eq2,
        $eq3,
    ];

    my $and1 := TypeConstraint.And($eq1, $eq2);
    my $and2 := TypeConstraint.And($eq1, $eq3);
    my $and3 := TypeConstraint.And($eq2, $eq3);
    my $and4 := TypeConstraint.And($eq1, $eq2, $eq3);

    test-classification($_, :isAtom(0), :isSimple(0), :isEq(0), :isAnd(1)) for [
        $and1,
        $and2,
        $and3,
        $and4,
    ];
}


{ # - .vars --------------------------------------------------------------------
    my %vs;
    my $s;

    my $True  := TypeConstraint.True;
    my $False := TypeConstraint.False;

    for [$True, $False] {
        $s := $_.Str;
        %vs := $_.vars;
        ok(nqp::ishash(%vs), ".vars of $s is-a hash");
        is(+%vs,         0,  ".vars of $s is empty");
    }

    my $Void  := Type.Void;
    my $Bool  := Type.BOOL;
    my $Str   := Type.Str;
    my $Int   := Type.Int;
    my $Num   := Type.Num;
    my $Array := Type.Array;

    my $v1 := Type.Var;
    my $eq1 := TypeConstraint.Eq($v1, $Str);
    my $eq2 := TypeConstraint.Eq($v1, Type.Sum($Int, $Str));
    my $eq3 := TypeConstraint.Eq($v1, Type.Cross($Int, $Str));
    my $v2 := Type.Var;
    my $eq4 := TypeConstraint.Eq($v1, $v2);
    my $eq5 := TypeConstraint.Eq($v1, Type.Sum($v2, $Str, $Int));
    my $eq6 := TypeConstraint.Eq($v2, Type.Cross($Str, $v1, $Int));
    my $eq7 := TypeConstraint.Eq($v2, Type.Cross($v2, $v1, $Int));
    my $v3 := Type.Var;
    my $eq8 := TypeConstraint.Eq($v1, Type.Sum($v1, $v2, $v3, $Int));

    for [$eq1, $eq2, $eq3, $eq4, $eq5, $eq6, $eq7, $eq8] {
        $s := $_.Str;
        %vs := $_.vars;
        ok(nqp::ishash(%vs),   ".vars of $s is-a hash");
        my %vsExpected := $_.lhs.vars;
        for $_.rhs.vars {
            %vsExpected{$_.key} := $_.value;
        }
        is(+%vs, +%vsExpected, ".vars of $s is the union of the left-hand-side's and ride-hand-side's .vars (a)");
        for %vsExpected {
            is(%vs{$_.key}, $_.value, ".vars of $s is the union of the left-hand-side's and ride-hand-side's .vars (b/" ~ $_.value.Str ~ ")");
        }
    }

    my $and1 := TypeConstraint.And($eq1, $eq2);
    my $and2 := TypeConstraint.And($eq3, $eq4, $eq5, $eq6, $eq7, $eq8);
    my $and3 := TypeConstraint.And($and1, $and2);

    for [$and1, $and2] {
        $s := $_.Str;
        %vs := $_.vars;
        ok(nqp::ishash(%vs),   ".vars of $s is-a hash");
        my %vsExpected := $_.head.vars;
        for $_.tail.vars {
            %vsExpected{$_.key} := $_.value;
        }
        is(+%vs, +%vsExpected, ".vars of $s is the union of the head's and tail's .vars (a)");
        for %vsExpected {
            is(%vs{$_.key}, $_.value, ".vars of $s is the union of the head's and tail's .vars (b/" ~ $_.value.Str ~ ")");
        }
    }
}




{ # - .subst -------------------------------------------------------------------
    my $s;

    my $Void  := Type.Void;
    my $Bool  := Type.BOOL;
    my $Str   := Type.Str;
    my $Int   := Type.Int;
    my $Num   := Type.Num;
    my $Array := Type.Array;
    my $v1 := Type.Var;
    my $v2 := Type.Var;
    my $v3 := Type.Var;
    my $v4 := Type.Var;

    my %subst := nqp::hash(
        $v1.name, $v2, 
        $v3.name, $Int
    );

    my $True  := TypeConstraint.True;
    my $False := TypeConstraint.False;

    my sub ignore(*@as, *%ns) {
        $False;
    }

    my sub test_subst($c, %subst, $expected) {
        my $substS := join(', ', %subst, :map(-> $_ { $_.key ~ ' => ' ~ $_.value.Str }));
        my $cS := $c.Str;
        my $expectedS := $expected.Str;
        is($c.subst(%subst, :onError(&ignore)).Str, $expectedS,
            #:describe(-> $_ { $_.Str }), # TODO: make constraints singletons
            ".subst($substS) on ($cS) yields ($expectedS)" ~ ($expected =:= $c ?? ' again' !! ''));
    }

    test_subst($_, %subst, $_)
        for [$True, $False];

    my $eq0 := TypeConstraint.Eq($v4, $Str);   # $v4 is not mapped
    test_subst($eq0, %subst, $eq0);

    my $eq1 := TypeConstraint.Eq($v1, $Str);
    my $eq2 := TypeConstraint.Eq($v2, $Str);
    test_subst($eq1, %subst, $eq2);

    test_subst(TypeConstraint.Eq($v3, $Int), %subst, $True);   # $v3 is mapped to Int
    test_subst(TypeConstraint.Eq($v3, $Str), %subst, $False);  # $v3 is mapped to Int

    my $eq2x := TypeConstraint.Eq($v1, Type.Sum($Int, $Str));
    my $eq3x := TypeConstraint.Eq($v1, Type.Cross($Int, $Str));

    my $eq4 := TypeConstraint.Eq($v1, $v2);
    my $eq5 := TypeConstraint.Eq($v1, Type.Sum($v2, $Str, $Int));
    my $eq6 := TypeConstraint.Eq($v2, Type.Cross($Str, $v1, $Int));
    my $eq7 := TypeConstraint.Eq($v2, Type.Cross($v2, $v1, $Int));
    
    my $eq8 := TypeConstraint.Eq($v1, Type.Sum($v1, $v2, $v3, $Int));

}


{ # - type constraints ---------------------------------------------------------

    my $Void     := Type.Void;
    my $DontCare := Type.DontCare;
    my $Bool     := Type.BOOL;
    my $Str      := Type.Str;
    my $Int      := Type.Int;
    my $Num      := Type.Num;
    my $Array    := Type.Array;
    my $var1 := Type.Var;
    my $var2 := Type.Var;

    my $fun1 := Type.Fn($Str, $Int);

    dies_ok({ Type.constrain() },                   'Type.constraint with no args');
    dies_ok({ Type.constrain($Int) },               'Type.constraint with one args');
    dies_ok({ Type.constrain($Int, $Int, $Int) },   'Type.constraint with three args');
    
    my $onErrorCalled;
    my sub onError(*@ps, *%ns) {
        $onErrorCalled := 1;
        #[@ps, %ns];
        TypeConstraint.False;
    }

    my sub error_ok($t1, $t2) {
        my $m;
        
        $m := 'constraining ' ~ $t1.Str ~ '  =  ' ~ $t2.Str;
        $onErrorCalled := 0;
        lives_ok({ Type.constrain($t1, $t2, :&onError) }, $m);
        ok($onErrorCalled, $m ~ ' yields Type error');

        $onErrorCalled := 0;
        $m := 'constraining ' ~ $t2.Str ~ '  =  ' ~ $t1.Str;
        lives_ok({ Type.constrain($t2, $t1, :&onError) }, $m);
        ok($onErrorCalled, $m ~ ' yields Type error');
    }

    error_ok($Str, $Int);

    error_ok($Int, Type.Fn($Str, $Int));
    error_ok($Num, Type.Fn($var1, $Num));

    error_ok($Int, Type.Cross($Str, $Int));
    error_ok($Num, Type.Cross($var1, $Num));


    error_ok(Type.Fn($Str, $Int), Type.Cross($Str, $Int));
    error_ok(Type.Fn($Str, $Int), Type.Cross($var1, $Num));
    error_ok(Type.Fn($var1, $Num), Type.Cross($Str, $Int));
    error_ok(Type.Fn($var1, $Num), Type.Cross($var1, $Num));
    

    error_ok(Type.Cross($Int, $Str), Type.Cross($Str, $Int));
    error_ok(Type.Cross($Str, $var1), Type.Cross($Str, $Int, $Num));

    my @types1 := [
        $Void,
        $DontCare,
        $Str,
        $Int,
        $Num,
        $Bool,
        $Array,
        $var1, $var2,
        $fun1,
        Type.Cross($Str, $Int),
        Type.Cross($Str, $Int, $Num),
        Type.Cross($fun1, $Num, $fun1),
    ];

    is(Type.constrain($_, $_), TypeConstraint.True, 'constraining (' ~ $_.Str ~ ') = itself ~> True')
        for @types1;

    my $sum1 := Type.Sum($Int, $Str);
    is(Type.constrain-sub($Int, $sum1), TypeConstraint.True, :describe(-> $_ { $_.Str }), 
        'constraining (' ~ $Int.Str ~ ') :< (' ~ $sum1.Str ~ ') ~> True');

    diag(TypeConstraint.Eq($Int, $Str).Str);

}



done();
