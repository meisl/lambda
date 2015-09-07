use testing;
use Util;

use Type;

plan(65);


{ # - class methods -----------------------------------------------------------
}


{ # - classification -----------------------------------------------------------
    my sub test-classification($t, *%adverbs) {
        isa_ok($t, TypeConstraint, |%adverbs, '(' ~ $t.Str ~ ') classification');
    }

    test-classification($_, :isAtom(1), :isSimple(1), :isEq(0)) for [
        TypeConstraint.True,
        TypeConstraint.False,
    ];

    test-classification($_, :isAtom(0), :isSimple(1), :isEq(1)) for [
        TypeConstraint.get(Type.Var, Type.Str),
        TypeConstraint.get(Type.Var, Type.Sum(Type.Int, Type.Str)),
        TypeConstraint.get(Type.Var, Type.Cross(Type.Int, Type.Str)),
    ];

}


{ # - type constraints ---------------------------------------------------------

    my $Str := Type.Str;
    my $Int := Type.Int;
    my $Num := Type.Num;
    my $fun1 := Type.Fn($Str, $Int);
    my $var1 := Type.Var;
    my $var2 := Type.Var;

    dies_ok({ Type.constrain() },                   'Type.constraint with no args');
    dies_ok({ Type.constrain($Int) },               'Type.constraint with one args');
    dies_ok({ Type.constrain($Int, $Int, $Int) },   'Type.constraint with three args');
    
    my $onErrorCalled;
    my sub onError(*@ps, *%ns) {
        $onErrorCalled := 1;
        [@ps, %ns];
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
        Type.Void,
        Type._,
        $Str,
        $Int,
        $Num,
        Type.BOOL,
        Type.Array,
        $var1, $var2,
        $fun1,
        Type.Cross($Str, $Int),
        Type.Cross($Str, $Int, $Num),
        Type.Cross($fun1, $Num, $fun1),
    ];

    is(Type.constrain($_, $_), TypeConstraint.True, 'constraining (' ~ $_.Str ~ ') to itself')
        for @types1;

}



done();
