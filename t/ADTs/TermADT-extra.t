use v6;
use Test;
use Test::Util;
use Test::Util_Lambda;
use Test::Util_List;
use Test::Util_Term;

use Lambda::BaseP6;
use Lambda::Boolean;


# module under test:
use Lambda::TermADT;

plan 53;


{ # Term->source
    is_properLambdaFn($Term2source, 'Term->source');

    testTermFn( $Term2source, :argToStr('`\'' ~ * ~ '\''),
        'x'                   => 'x',
        '"c"'                 => '"c"',
        '5'                   => '5',
        'x "c"'               => '(x "c")',
        'x x'                 => '(x x)',
        'x y'                 => '(x y)',
        'λx."c"'              => '(λx."c")',
        'λx.x'                => '(λx.x)',
        'λx.x x'              => '(λx.(x x))',
        'λx.x "c"'            => '(λx.(x "c"))',
        'λx.x y'              => '(λx.(x y))',
        'λx.y x'              => '(λx.(y x))',
        'λx.x (λy.x y)'       => '(λx.(x (λy.(x y))))',
        '(λy.x y) y'          => '((λy.(x y)) y)',
        '(λx.y x) (λy.x y)'   => '((λx.(y x)) (λy.(x y)))',
        'λx.(λy.z y) x'       => '(λx.((λy.(z y)) x))',
        'λx.(λy.x y) x'       => '(λx.((λy.(x y)) x))',
        'λx.(λx.x y) x'       => '(λx.((λx.(x y)) x))',
    );
}


{ # Term->srcLess
    is_properLambdaFn($Term2srcLess, 'Term->srcLess');

    testTermFn( $Term2srcLess,
        'x'                   => 'x',
        '"c"'                 => '"c"',
        '5'                   => '5',
        'x "c"'               => '(x "c")',
        'x x'                 => '(x x)',
        'x y'                 => '(x y)',
        'x y z'               => '(x y z)',
        'x y z x'             => '(x y z x)',
        'x (y z)'             => '(x (y z))',
        'x (y z) x'           => '(x (y z) x)',
        'x (y (z x))'         => '(x (y (z x)))',

        'λx."c"'              => 'λx."c"',
        'λx.x'                => 'λx.x',
        'λx.x x'              => 'λx.x x',
        'λx.x "c"'            => 'λx.x "c"',
        'λx.x y'              => 'λx.x y',
        'λx.x (λy.x y)'       => 'λx.x (λy.x y)',
        'λx.(λy.z y) x'       => 'λx.(λy.z y) x',
        'λx.(λy.z y) (x x)'   => 'λx.(λy.z y) (x x)',
        'λz.x (λy.x y)'       => 'λz.x (λy.x y)',

        'x (λy.x y)'              => '(x (λy.x y))',
        'x y (y z)'               => '(x y (y z))',
        'x y (λy.x y)'            => '(x y (λy.x y))',
        '(λy.x y) y'              => '(λy.x y) y',
        '(λx.y x) (λy.x y)'       => '(λx.y x) (λy.x y)',
        '(λx.y x) (x y)'          => '(λx.y x) (x y)',
        '(λx.y x) (x y) x'        => '(λx.y x) (x y) x',
        '(λx.y x) (x y) (λx.x)'   => '(λx.y x) (x y) (λx.x)',
        '(λx.y x) (λx.x) (λx.x)'  => '(λx.y x) (λx.x) (λx.x)',
    );
}


{ # Term->children
    is_properLambdaFn($Term2children, 'Term->children');

    my ($x, $y, $c) = `'x', `'y', `'"c"';
    my $cs;

    $cs = $Term2children($x);
    $has_length($cs, 0, "(Term->children $x) / a VarT has no children");

    $cs = $Term2children($c);
    $has_length($cs, 0, "(Term->children $c) / a ConstT has no children");
    
    my $t1 = `'(x y)';
    $cs = $Term2children($t1);
    $has_length($cs, 2, "(Term->children $t1) / an AppT has two children (func and arg)");
    $contains_ok($x, $cs, "(Term->children $t1)");
    $contains_ok($y, $cs, "(Term->children $t1)");
    
    my $t2 = `'((x y) "c")';
    $cs = $Term2children($t2);
    $has_length($cs, 2, "(Term->children $t2) / an AppT has two children (func and arg)");
    $contains_ok($t1, $cs, "(Term->children $t2)") or die;
    $contains_ok($c,  $cs, "(Term->children $t2)");
    
    my $t3 = `'(λx.((x y) "c"))';
    $cs = $Term2children($t3);
    $has_length($cs, 1, "(Term->children $t3) / a LamT has one child (its body)");
    $contains_ok($t2, $cs, "(Term->children $t3)");
}


{ # predicate selfApp?
    is_properLambdaFn($is-selfApp, 'selfApp?');

    testTermFn( $is-selfApp, :expectedToStr(*.Str),
        'x'           => $false,
        '"c"'         => $false,
        '5'           => $false,
        'x "c"'       => $false,
        'x x'         => $true, 
        'y y'         => $true, 
        'x y'         => $false,
        'λx."c"'      => $false,
        'λx.x'        => $false,
        'ωX'          => $false,  # 'λx.x x
        'ωY'          => $false,  # 'λy.y y
        'λx.x "c"'    => $false,
        'λx.x y'      => $false,
        'λx.y x'      => $false,
        'ΩXX'         => $false,  # (ωX ωX)
        'ΩYY'         => $false,  # (ωY ωY)
    );
}


{ # predicate selfAppOfVar?
    is_properLambdaFn($is-selfAppOfVar, 'selfAppOfVar?');

    my ($x, $y, $c) = `'x', `'y', `'"c"';
    my $f = $is-selfAppOfVar($x) but Definition("{$is-selfAppOfVar.name} $x");

    testTermFn($f, :expectedToStr(*.Str),
        'x'           => $false,
        '"c"'         => $false,
        '5'           => $false,
        'x "c"'       => $false,
        'x x'         => $true, 
        'y y'         => $false,  # [wrong var]
        'x y'         => $false,
        'λx."c"'      => $false,
        'λx.x'        => $false,
        'ωX'          => $false,  # 'λx.(x x)
        'ωY'          => $false,  # 'λy.(y y)
        'λx.x "c"'    => $false,
        'λx.x y'      => $false,
        'λx.y x'      => $false,
        'ΩXX'         => $false,  # (ωX ωX)
        'ΩYY'         => $false,  # (ωY ωY)
    );

    $f = $is-selfAppOfVar($y) but Definition("{$is-selfAppOfVar.name} $y");
    testTermFn($f, :expectedToStr(*.Str),
        'x'           => $false,
        '"c"'         => $false,
        '5'           => $false,
        'x "c"'       => $false,
        'x x'         => $false,  #   [wrong var]
        'y y'         => $true, 
        'x y'         => $false,
        'λx."c"'      => $false,
        'λx.x'        => $false,
        'ωX'          => $false,  # λx.x x
        'ωY'          => $false,  # λy.y y
        'λx.x "c"'    => $false,
        'λx.x y'      => $false,
        'λx.y x'      => $false,
        'ΩXX'         => $false,  # (ωX ωX)
        'ΩYY'         => $false,  # (ωY ωY)
    );

    $f = $is-selfAppOfVar($c) but Definition("{$is-selfAppOfVar.name} $c");
    testTermFn($f, :expectedToStr(*.Str),
        'x'           => $false,
        '"c"'         => $false,
        '5'           => $false,
        'x "c"'       => $false,
        'x x'         => $false,  #   [passed a ConstT as 1st arg]
        'y y'         => $false,  #   [passed a ConstT as 1st arg]
        'x y'         => $false,
        'λx."c"'      => $false,
        'λx.x'        => $false,
        'ωX'          => $false,  # λx.x x
        'ωY'          => $false,  # λy.y y
        'λx.x "c"'    => $false,
        'λx.x y'      => $false,
        'λx.y x'      => $false,
        'ΩXX'         => $false,  # (ωX ωX)
        'ΩYY'         => $false,  # (ωY ωY)
    );
}


{ # predicate omega?
    is_properLambdaFn($is-omega, 'ω?');

    testTermFn( $is-omega, :expectedToStr(*.Str),
        'x'           => $false,
        '"c"'         => $false,
        '5'           => $false,
        'x "c"'       => $false,
        'x x'         => $false,
        'y y'         => $false,
        'x y'         => $false,
        'λx."c"'      => $false,
        'λx.x'        => $false,
        'ωX'          => $true,   # λx.x x
        'ωY'          => $true,   # λy.y y
        'λy.x x'      => $false,  # wrong binder
        'λx.x y'      => $false,
        'λx.y x'      => $false,
        'λx.x "c"'    => $false,
        'ΩXX'         => $false,  # (ωX ωX)
        'ΩYY'         => $false,  # (ωY ωY)
    );
}


{ # predicate Ω? ($is-Omega)
    is_properLambdaFn($is-Omega, 'Ω?');

    testTermFn( $is-Omega, :expectedToStr(*.Str),
        'x'                 => $false,
        '"c"'               => $false,
        '5'                 => $false,
        'x "c"'             => $false,
        'x x'               => $false,
        'y y'               => $false,
        'x y'               => $false,
        'λx."c"'            => $false,
        'λx.x'              => $false,
        'ωX'                => $false,  # λx.x x
        'ωY'                => $false,  # λy.y y
        'λx.x "c"'          => $false,
        'λx.x y'            => $false,
        'λx.y x'            => $false,
        'ΩXX'               => $true ,  # (ωX ωX)
        'ΩXY'               => $true ,  # (ωX ωY)
        'ΩYX'               => $true ,  # (ωY ωX)
        'ΩYY'               => $true,   # (ωY ωY)
        '(λx.x x) (λy.x x)' => $false,  # wrong binder in 2nd λ
        '(λx.x x) (y y)'    => $false,
        'y y (λx.x x)'      => $false,
    );
}


{ # Term->size
    is_properLambdaFn($Term2size, 'Term->size');

    # size of a LamT is 1 + size of body
    # size of an AppT is 1 + size of func + size of arg
    # size of both, a VarT and ConstT is 1

    testTermFn( $Term2size, :expectedToStr(*.Str),
        'x'                   =>  1,
        '"c"'                 =>  1,
        '5'                   =>  1,
        'x "c"'               =>  3,
        'x (x y)'             =>  5,
        'λz.x (x y)'          =>  6,
        'λx.x (λy.x y)'       =>  7,
        '(λy.x y) y'          =>  6,
        '(λx.y x) (λy.x y)'   =>  9,
        'λx.(λy.z y) x'       =>  7,
        'ωX'                  =>  4,  # λx.x x
        'ωY'                  =>  4,  # λy.y y
        'ΩXX'                 =>  9,  # (ωX ωX)
        'ΩXY'                 =>  9,  # (ωX ωY)
        'ΩYX'                 =>  9,  # (ωY ωX)
        'ΩYY'                 =>  9,  # (ωY ωY)
    );

}


# VarT special ----------------------------------------------------------------

{ # (VarT Str)
    my $x1 = $VarT('x');
    my $x2 = $VarT('x');

    cmp_ok($x1, '===', $x2, '(VarT Str) returns same var for same name');
    
    my $y1 = $VarT('y');
    nok($y1 === $x1, '(VarT Str) returns new instance if necessary')
        or diag "expected $y1 to be different from $x1";
    is($VarT2name($y1), 'y', '(VarT Str) returns new instance if necessary');
    my $y2 = $VarT('y');
    cmp_ok($y1, '===', $y2, '(VarT Str) returns same var for same name');
}

{ # fresh-var-for
    is_properLambdaFn($fresh-var-for, 'fresh-var-for');

    dies_ok( { $fresh-var-for(`'x y')  }, '$fresh-var-for does not accept an AppT arg');
    dies_ok( { $fresh-var-for(`'λx.x') }, '$fresh-var-for does not accept a LamT arg');
    dies_ok( { $fresh-var-for(`'"c"')  }, '$fresh-var-for does not accept a ConstT arg');

    my $fresh1 = $fresh-var-for(`'x');
    my $fresh2 = $fresh-var-for(`'x');

    isnt($VarT2name($fresh1), $VarT2name(`'x'), "fresh var has name different from any other");
    isnt($VarT2name($fresh1), $VarT2name(`'y'), "fresh var has name different from any other");
    isnt($VarT2name($fresh1), $VarT2name($fresh2), "fresh var has name different from any other");

    my $fresh3 = $fresh-var-for(`'x');

    isnt($VarT2name($fresh3), $VarT2name(`'x'), "fresh var has name different from any other");
    isnt($VarT2name($fresh3), $VarT2name(`'y'), "fresh var has name different from any other");
    isnt($VarT2name($fresh3), $VarT2name($fresh1), "fresh var has name different from any other");
    isnt($VarT2name($fresh3), $VarT2name($fresh2), "fresh var has name different from any other");

    my $xname = $VarT2name(`'x');
    ok($fresh3.gist ~~ / '/' $xname /, ".fresh(:for).gist contains the given var's gist")
        or diag "# got: {$fresh3.gist}";
    nok($VarT2name($fresh3) ~~ / $xname /, ".fresh(:for).name does NOT contain the given var's name");
    cmp_ok $fresh3, '===', $VarT($VarT2name($fresh3)), "can get back same instance of fresh var via VarT.get";

    my $fresh4 = $fresh-var-for($fresh3);

    isnt($VarT2name($fresh4), $VarT2name(`'x'), "fresh var has name different from any other");
    isnt($VarT2name($fresh4), $VarT2name(`'y'), "fresh var has name different from any other");
    isnt($VarT2name($fresh4), $VarT2name($fresh1), "fresh var has name different from any other");
    isnt($VarT2name($fresh4), $VarT2name($fresh2), "fresh var has name different from any other");
    isnt($VarT2name($fresh4), $VarT2name($fresh3), "fresh var has name different from any other");

    my $f3name = $VarT2name($fresh3);
    ok($fresh4.gist ~~ / $f3name /, ".fresh(:for).gist contains the given var's gist")
        or diag "# got: {$fresh4.gist}";
    nok($VarT2name($fresh4) ~~ / $f3name /, ".fresh(:for).name does NOT contain the given var's name");
    cmp_ok $fresh3, '===', $VarT($VarT2name($fresh3)), "can get back same instance of fresh var via VarT.get";
}
