use v6;
use Test;
use Test::Util;
use Test::Util_Lambda;
use Test::Util_List;

use Lambda::Boolean;
use Lambda::MaybeADT;
use Lambda::ListADT;
use Lambda::TermADT;


# module under test:
use Lambda::FreeVars;

plan 88;


my $w = $VarT('w');
my $x = $VarT('x');
my $y = $VarT('y');
my $z = $VarT('z');
my $c = $ConstT('x');   # Yes, use "x" as value!

my sub test($f, :$argToStr = *.Str, :$expToStr, *@tests) {
    for @tests -> $test {
        my $args        = $test.key;
        my $argStr      = $argToStr($args);
        my $expected    = $test.value;
        my $expectedStr = $expToStr.defined
                            ?? ' -> ' ~ $expToStr($expected)
                            !! '';
        my $desc        = "($f $argStr)$expectedStr";

        is($f(|$args), $expected, $desc);
    }
}

my sub test-pred($f, *@tests) {
    test($f,
        :argToStr(-> $args { $args.map($Term2source).join(' ') }),
        :expToStr(-> $x {$x.Str}),
        @tests
    );
}

{ # predicate free?
    is_properLambdaFn($is-free);

    is $is-free.symbol, 'free?', '$is-free.symbol';
    is $is-free.Str,    'free?', '$is-free.Str';

    my $app = $AppT($x, $y);    # (x y)
    my $lam = $LamT($x, $app);  # λx.x y

    test-pred( $is-free,
        [$x, $c]    => $false,      # x in c
        [$x, $x]    => $true,       # x in x
        [$x, $y]    => $false,      # x in y
        [$x, $app]  => $true,       # x in (x y)
        [$y, $app]  => $true,       # y in (x y)
        [$x, $lam]  => $false,      # x in λx.x y
        [$y, $lam]  => $true,       # y in λx.x y
    );

    dies_ok( { $is-free(TTerm,  $x)     }, "free? requires defined TTerm as 1st arg");
    dies_ok( { $is-free($x,     TTerm)  }, "free? requires defined TTerm as 2nd arg");
    dies_ok( { $is-free($c,     $x)     }, "free? yields error if 1st arg is a ConstT");
    dies_ok( { $is-free($app,   $x)     }, "free? yields error if 1st arg is an AppT");
    dies_ok( { $is-free($lam,   $x)     }, "free? yields error if 1st arg is an LamT");
}


{ #predicate free-under?
    is_properLambdaFn($is-free-under);

    is $is-free-under.symbol, 'free-under?', '$is-free-under.symbol';
    is $is-free-under.Str,    'free-under?', '$is-free-under.Str';

    my $a1 = $AppT($x,  $y);            # (x y)
    my $l1 = $LamT($x,  $a1);           # λx.x y
    my $l2 = $LamT($z,  $AppT($z, $y)); # λz.z y
    my $a2 = $AppT($l1, $z);            # ((λx.x y) z)
    my $a3 = $AppT($z,  $l1);           # (z (λx.x y))
    my $a4 = $AppT($l1, $l2);           # ((λx.x y) (λz.z y))

    test-pred( $is-free-under,
        # never under any binder in a ConstT:
        [$x, $x, $c]    => $false,
        [$x, $y, $c]    => $false,
        [$x, $z, $c]    => $false,

        # never under any binder in a VarT:
        [$x, $x, $x]    => $false,
        [$x, $y, $x]    => $false,
        [$x, $z, $x]    => $false,

        # never under any binder in a simple AppT of VarTs [ a1: (x y) ]:
        [$x, $x, $a1]   => $false,
        [$x, $y, $a1]   => $false,
        [$x, $z, $a1]   => $false,
        [$y, $x, $a1]   => $false,
        [$y, $y, $a1]   => $false,
        [$y, $z, $a1]   => $false,

        # never under any binder if it doesn't occur at all [ a1: (x y) ]:
        [$w, $x, $a1]   => $false,
        [$w, $y, $a1]   => $false,
        [$w, $z, $a1]   => $false,

        # a2: ((λx.x y) z); x and y do occur in ((λx.x y) z)
        [$x, $x, $a2]   => $false,
        [$x, $y, $a2]   => $false,
        [$x, $z, $a2]   => $false,

        [$y, $x, $a2]   => $true,   # y is free only under x in ((λx.x y) z)
        [$y, $y, $a2]   => $false,
        [$y, $z, $a2]   => $false,

        # w doesn't occur at all in a2: ((λx.x y) z)
        [$w, $x, $a2]   => $false,
        [$w, $y, $a2]   => $false,
        [$w, $z, $a2]   => $false,

        # a3: (z (λx.x y))
        [$x, $x, $a3]   => $false,  # x is never free since it's bound in (z (λx.x y))
        [$x, $y, $a3]   => $false,
        [$x, $z, $a3]   => $false,

        [$y, $x, $a3]   => $true,   # y is free only under x in (z (λx.x y))
        [$y, $y, $a3]   => $false,
        [$y, $z, $a3]   => $false,

        [$w, $x, $a3]   => $false,  # w never occurs in (z (λx.x y))
        [$w, $y, $a3]   => $false,
        [$w, $z, $a3]   => $false,

        # a4: ((λx.x y) (λz.z y))
        [$x, $x, $a4]   => $false,  # x is never free since it's bound in func and doesn't occur in arg
        [$x, $y, $a4]   => $false,
        [$x, $z, $a4]   => $false,

        [$y, $x, $a4]   => $true,   # y is free under x in func
        [$y, $y, $a4]   => $false,
        [$y, $z, $a4]   => $true,   # y is free under z in arg

        [$w, $x, $a4]   => $false,  # x is never free since it doesn't occur anywhere
        [$w, $y, $a4]   => $false,
        [$w, $z, $a4]   => $false,

    );
}

{ # free-var
    is_properLambdaFn($free-var);

    my $app = $AppT($x, $y);    # '(x y)'
    my $lam = $LamT($x, $app);  # 'λx.x y'

    is($free-var('x', $c),   $None,     "($free-var 'x' $c)");
    is($free-var('x', $x),   $Some($x), "($free-var 'x' $x)");

    is($free-var('x', $y),   $None,     "($free-var 'x' $y)");

    is($free-var('x', $app), $Some($x), "($free-var 'x' $app)");
    is($free-var('y', $app), $Some($y), "($free-var 'y' $app)");

    is($free-var('x', $lam), $None,     "($free-var 'x' $lam)");
    is($free-var('y', $lam), $Some($y), "($free-var 'y' $lam)");
}

{ # free-vars
    is_properLambdaFn($free-vars);

    my $app1 = $AppT($x, $y);       # (x y)
    my $app2 = $AppT($x, $x);       # (x x)
    my $lam1 = $LamT($x, $app1);    # λx.x y
    my $app3 = $AppT($x, $lam1);    # (x λx.x y)
    my $app4 = $AppT($app3, $c);    # (x λx.x y) c
    my $app5 = $AppT($c, $app3);    # c (x λx.x y)

    is($free-vars($c),   $nil,              "($free-vars $c)");
    is($free-vars($x),   $cons($x, $nil),   "($free-vars $x)");

    is($free-vars($y),   $cons($y, $nil),   "($free-vars $y)");

    my $fvs;

    $fvs = $free-vars($app1);
    $has_length($fvs, 2, "($free-vars $app1)");
    $contains_ok($x, $fvs, "(free-vars $app1)");
    $contains_ok($y, $fvs, "(free-vars $app1)");

    $fvs = $free-vars($app2);
    $has_length($fvs, 1, "($free-vars $app2) should not contain duplicates");
    $contains_ok($x, $fvs, "(free-vars $app2)");

    $fvs = $free-vars($lam1);
    $has_length($fvs, 1, "($free-vars $lam1)");
    $contains_ok($y, $fvs, "(free-vars $lam1)");

    $fvs = $free-vars($app3);
    $has_length($fvs, 2, "($free-vars $app3)");
    $contains_ok($x, $fvs, "(free-vars $app3)");
    $contains_ok($y, $fvs, "(free-vars $app3)");

    $fvs = $free-vars($app4);
    $has_length($fvs, 2, "($free-vars $app4)");
    $contains_ok($x, $fvs, "(free-vars $app4)");
    $contains_ok($y, $fvs, "(free-vars $app4)");

    $fvs = $free-vars($app5);
    $has_length($fvs, 2, "($free-vars $app5)");
    $contains_ok($x, $fvs, "(free-vars $app5)");
    $contains_ok($y, $fvs, "(free-vars $app5)");
}
