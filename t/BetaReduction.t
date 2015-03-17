use v6;
use Test;
use Test::Util;
use Test::Util_Lambda;
use Test::Util_List;

use Lambda::Boolean;
use Lambda::MaybeADT;
use Lambda::ListADT;
use Lambda::TermADT;

use Lambda::Conversion::Bool-conv;

use Lambda::P6Currying;

# module under test:
use Lambda::BetaReduction;

plan 119;


my $g = $VarT('g');
my $h = $VarT('h');
my $k = $VarT('k');
my $u = $VarT('u');
my $v = $VarT('v');
my $x = $VarT('x');
my $y = $VarT('y');
my $z = $VarT('z');
my $c = $ConstT('c');

my $yz = $AppT($y, $z);


# [O|o]mega: Omega (with capital O) is a (the) lambda term that beta-contracts to itself (modulo alpha-conversion).
my $omegaX  = $LamT('x', $AppT($x, $x));  # (λx.x x)
my $OmegaXX = $AppT($omegaX, $omegaX);   # ((λx.x x) (λx.x x))
my $omegaY  = $LamT('y', $AppT($y, $y));  # (λy.y y)
my $OmegaYY = $AppT($omegaY, $omegaY);   # ((λy.y y) (λy.y y))
my $OmegaXY = $AppT($omegaX, $omegaY);   # ((λx.x x) (λy.y y))


{ # predicate betaRedex?
    is_properLambdaFn($is-betaRedex, 'betaRedex?');

    my sub is_betaRedex(*@tests) {
        for @tests -> $test {
            my $term       = $test.key;
            my $termStr    = $Term2source($term);
            my $expected   = $test.value;
            my $expectedP6 = convertTBool2P6Bool($expected);
            my $desc       = $expectedP6
                                ?? "$termStr IS a beta redex" 
                                !! "$termStr is not a beta redex";
            cmp_ok($is-betaRedex($term), '===', $expected, $desc);
        }
    }

    is_betaRedex(
        $x                                                          => $false,  # x
        $c                                                          => $false,  # "c"
        $LamT('x', $c)                                              => $false,  # λx."c"
        $LamT('x', $x)                                              => $false,  # λx.x
        $LamT('x', $AppT($x, $c))                                   => $false,  # λx.x "c"
        $LamT('x', $AppT($x, $y))                                   => $false,  # λx.x y
        $LamT('x', $AppT($y, $x))                                   => $false,  # λx.y x
        $LamT('x', $AppT($x, $AppT($LamT('y', $LamT('z', $AppT($y, $x))), $LamT('y', $AppT($x, $y)))))          # not a redex but contractible (twice)
            => $false,  # λx.x ((λy.λz.y x) (λy.x y))
        $AppT($x, $c)                                               => $false,  # (x c)
        $AppT($x, $x)                                               => $false,  # (x x)
        $AppT($x, $y)                                               => $false,  # (x y)
        $AppT($LamT('x', $y), $x)                                   => $true,   # ((λx.y) x)                # a redex
        $AppT($LamT('x', $AppT($AppT($z, $x), $y)), $c)             => $true,   # ((λx.z x y) "c")          # a redex
        $AppT($AppT($LamT('y', $AppT($x, $y)), $y), $z)             => $false,  # (((λy.x y) y) z)          # not a redex but reducible
        $AppT($y, $AppT($LamT('y', $AppT($x, $y)), $z))             => $false,  # (y ((λy.x y) z))          # not a redex but reducible
        $AppT($LamT('y', $AppT($x, $y)), $z)                        => $true,   # ((λy.x y) z)              # a redex
        $AppT($AppT($LamT('x', $y), $x), $AppT($LamT('y', $x), $y)) => $false,  # (((λx.y) x) ((λy.x) y))   # not a redex but reducible
        $LamT('x', $AppT($AppT($LamT('y', $AppT($z, $y)), $x), $x)) => $false,  # (λx.(λy.z y) x x)         # not a redex but reducible
        $omegaX                                                     => $false,  # (λx.x x)
        $OmegaXX                                                    => $true,   # ((λx.x x) (λx.x x))       # a redex, contracting to itself
        $omegaY                                                     => $false,  # (λy.y y)
        $OmegaYY                                                    => $true,   # ((λy.y y) (λy.y y))       # a redex, contracting to itself
        $OmegaXY                                                    => $true,   # ((λx.x x) (λy.y y))       # a redex, contracting to itself (module alpha-conv)
    );
}

{ # predicate betaReducible?
    is_properLambdaFn($is-betaReducible, 'betaReducible?');

    my sub is_betaReducible(*@tests) {
        for @tests -> $test {
            my $term       = $test.key;
            my $termStr    = $Term2source($term);
            my $expected   = $test.value;
            my $expectedP6 = convertTBool2P6Bool($expected);
            my $desc       = $expectedP6
                                ?? "$termStr IS beta-reducible"
                                !! "$termStr is not beta-reducible";
            cmp_ok($is-betaReducible($term), '===', $expected, $desc);
        }
    }

    is_betaReducible(
        $x                                                          => $false,  # x
        $c                                                          => $false,  # "c"
        $LamT($x, $c)                                               => $false,  # λx."c"
        $LamT($x, $x)                                               => $false,  # λx.x
        $LamT($x, $AppT($x, $c))                                    => $false,  # λx.x "c"
        $LamT($x, $AppT($x, $y))                                    => $false,  # λx.x y
        $LamT($x, $AppT($y, $x))                                    => $false,  # λx.y x
        $LamT($x, $AppT($x, $AppT($LamT($y, $LamT($z, $AppT($y, $x))), $LamT($y, $AppT($x, $y)))))          # not a redex but contractible (twice)
            => $true,  # λx.x ((λy.λz.y x) (λy.x y))
        $AppT($x, $c)                                               => $false,  # (x c)
        $AppT($x, $x)                                               => $false,  # (x x)
        $AppT($x, $y)                                               => $false,  # (x y)
        $AppT($LamT($x, $y), $x)                                    => $true,   # ((λx.y) x)                # a redex
        $AppT($LamT($x, $AppT($AppT($z, $x), $y)), $c)              => $true,   # ((λx.z x y) "c")          # a redex
        $AppT($AppT($LamT($y, $AppT($x, $y)), $y), $z)              => $true,   # (((λy.x y) y) z)          # not a redex but reducible
        $AppT($y, $AppT($LamT($y, $AppT($x, $y)), $z))              => $true,   # (y ((λy.x y) z))          # not a redex but reducible
        $AppT($LamT($y, $AppT($x, $y)), $z)                         => $true,   # ((λy.x y) z)              # a redex
        $AppT($AppT($LamT($x, $y), $x), $AppT($LamT($y, $x), $y))   => $true,   # (((λx.y) x) ((λy.x) y))   # not a redex but reducible
        $LamT($x, $AppT($AppT($LamT($y, $AppT($z, $y)), $x), $x))   => $true,   # (λx.(λy.z y) x x)         # not a redex but reducible
        $omegaX                                                     => $false,  # (λx.x x)
        $OmegaXX                                                    => $true,   # ((λx.x x) (λx.x x))       # a redex, contracting to itself
        $omegaY                                                     => $false,  # (λy.y y)
        $OmegaYY                                                    => $true,   # ((λy.y y) (λy.y y))       # a redex, contracting to itself
        $OmegaXY                                                    => $true,   # ((λx.x x) (λy.y y))       # a redex, contracting to itself (module alpha-conv)
        
        $AppT($LamT($x, $AppT($x, $x)), $yz)                        => $true,   # ((λx.(x x)) (y z)) # only "half of" Omega
    );

}


{ # function betaContract
    is_properLambdaFn($betaContract, 'betaContract');

    my sub betaContractsTo(*@tests) {
        for @tests -> $test {
            my $term     = $test.key;
            my $termStr  = $Term2source($term);
            my $expected = $test.value;
            my $toItself = $expected === $None;
            my $expStr  = $toItself
                ?? "itself (None)"
                !! '(Some ' ~ $Term2source($Some2value($expected)) ~ ')';
            my $desc = "$termStr beta-contracts to $expStr";

            my $actual = $betaContract($term);
            is($actual, $expected, $desc)
                or diag($actual.perl) and die;
        }
    }

    betaContractsTo(
        $x                                                          => $None,  # x
        $c                                                          => $None,  # "c"
        $LamT($x, $c)                                               => $None,  # λx."c"
        $LamT($x, $x)                                               => $None,  # λx.x
        $LamT($x, $AppT($x, $c))                                    => $None,  # λx.x "c"
        $LamT($x, $AppT($x, $y))                                    => $None,  # λx.x y
        $LamT($x, $AppT($y, $x))                                    => $None,  # λx.y x
        $LamT($x, $AppT($x, $AppT($LamT($y, $LamT($z, $AppT($y, $x))), $LamT($y, $AppT($x, $y)))))   # not a redex but contractible (twice)
            => $Some($LamT($x, $AppT($x, $LamT($z, $AppT($LamT($y, $AppT($x, $y)), $x))))),  # λx.x ((λy.λz.y x) (λy.x y)) -> λx.x (λz.(λy.x y) x)
        $AppT($x, $c)                                               => $None,  # (x c)
        $AppT($x, $x)                                               => $None,  # (x x)
        $AppT($x, $y)                                               => $None,  # (x y)
        $AppT($LamT($x, $y), $x)                                    => $Some($y),                       # a redex
            # ((λx.y) x) -> y
        $AppT($LamT($x, $AppT($AppT($z, $x), $y)), $c)              => $Some($AppT($AppT($z, $c), $y)), # a redex
            # ((λx.z x y) "c") -> (z "c" y)
        $AppT($AppT($LamT($y, $AppT($x, $y)), $y), $z)              => $Some($AppT($AppT($x, $y), $z)), # not a redex but reducible
            # (((λy.x y) y) z) -> (x y z)
        $AppT($y, $AppT($LamT($y, $AppT($x, $y)), $z))              => $Some($AppT($y, $AppT($x, $z))), # not a redex but reducible
            # (y ((λy.x y) z)) -> (y (x z))
        
        # see below for (((λx.y) x) ((λy.x) y))   # not a redex but contractible (twice)

        $LamT($x, $AppT($AppT($LamT($y, $AppT($z, $y)), $x), $x))   => $Some($LamT($x, $AppT($AppT($z, $x), $x))),  # not a redex but reducible
            # (λx.(λy.z y) x x) -> (λx.z x x)
        $omegaX                                                     => $None,               # (λx.x x)
        $OmegaXX                                                    => $None,               # ((λx.x x) (λx.x x))   # a redex, contracting to itself
        $omegaY                                                     => $None,               # (λy.y y)
        $OmegaYY                                                    => $None,               # ((λy.y y) (λy.y y))   # a redex, contracting to itself
        $OmegaXY                                                    => $Some($OmegaYY),     # ((λx.x x) (λy.y y))   # a redex, contracting to itself (module alpha-conv)
        
        $AppT($LamT($x, $AppT($x, $x)), $yz)                        => $Some($AppT($yz, $yz)),  # ((λx.(x x)) (y z)) # only "half of" Omega
    );

    my ($t, $bcd1, $bcd2, $expectedBrd);

    # (((λx.y) x) ((λy.x) y)) can contract twice; NO prescribed order!
    $t = $AppT($AppT($LamT($x, $y), $x), $AppT($LamT($y, $x), $y));
    subtest({
        $bcd1 = $betaContract($t);
        is($is-Some($bcd1), $true, "{$Term2source($t)} should beta-contract (at least) once") or die;
        $bcd1 = $Some2value($bcd1);
        # Note: we don't restrict the order in which parts are being contracted
        is($is-betaReducible($bcd1), $true, "(Some->value (betaContract {$Term2source($t)})) should still be beta-reducible") or die;
        
        $bcd2 = $betaContract($bcd1);
        is($is-Some($bcd2), $true, "{$Term2source($bcd1)} should beta-contract once more") or die;
        $bcd2 = $Some2value($bcd2);
        is($is-betaReducible($bcd2), $false,
            "(Some->value (betaContract {$Term2source($bcd1)})) should not be beta-reducible any further") or die;

        $expectedBrd = $AppT($y, $x);
        is($bcd2, $expectedBrd,
            "beta-contracting {$Term2source($t)} should yield {$Term2source($expectedBrd)}");
    }, "{$Term2source($t)} can contract twice; NO prescribed order!");


    subtest({ # a term that β-"contracts" to an ever larger term: (λx.x x y)(λx.x x y)
        my $t = {
            my $lx-xxy  = $LamT('x', $AppT($AppT($x, $x), $y)); # lam(<x>, <x x y>)
            $AppT($lx-xxy, $lx-xxy);
        }();

        # size of a LamT is 1 + size of body
        # size of an AppT is 1 + size of func + size of arg
        # size of both, a VarT and ConstT is 1
        my $s = $Term2size($t);
        is($s, 13, "(eq? 13 (Term->size {$Term2source($t)}))");

        $t = $Some2value($betaContract($t));
        $s = $Term2size($t);
        is($s, 15, "(eq? 15 (Term->size {$Term2source($t)}))");

        $t = $Some2value($betaContract($t));
        $s = $Term2size($t);
        is($s, 17, "(eq? 17 (Term->size {$Term2source($t)}))");

        $t = $Some2value($betaContract($t));
        $s = $Term2size($t);
        is($s, 19, "(eq? 19 (Term->size {$Term2source($t)}))");
    }, 'a term that β-"contracts" to an ever larger term: (λx.x x y)(λx.x x y)');
}


{ # function betaReduce
    is_properLambdaFn($betaReduce, 'betaReduce');

    my sub betaReducesTo(*@tests) {
        for @tests -> $test {
            my $term     = $test.key;
            my $termStr  = $Term2source($term);
            my $expected = $test.value;
            my $toItself = $expected === $None;
            my $expStr = $toItself
                ?? "itself (None)"
                !! '(Some ' ~ $Term2source($Some2value($expected)) ~ ')';
            my $desc = "$termStr beta-reduces to $expStr";

            my $actual = $betaReduce($term);
            is($actual, $expected, $desc)
                or diag($actual.perl) ;
        }
    }


    betaReducesTo(
        $x                                                          => $None,  # x
        $c                                                          => $None,  # "c"
        $LamT($x, $c)                                               => $None,  # λx."c"
        $LamT($x, $x)                                               => $None,  # λx.x
        $LamT($x, $AppT($x, $c))                                    => $None,  # λx.x "c"
        $LamT($x, $AppT($x, $y))                                    => $None,  # λx.x y
        $LamT($x, $AppT($y, $x))                                    => $None,  # λx.y x
        $LamT($x, $AppT($x, $AppT($LamT($y, $LamT($z, $AppT($y, $x))), $LamT($y, $AppT($x, $y)))))   # not a redex but contractible (twice)
            => $Some($LamT($x, $AppT($x, $LamT($z, $AppT($x, $x))))),  # λx.x ((λy.λz.y x) (λy.x y)) -> λx.x (λz.x x)
        $AppT($x, $c)                                               => $None,  # (x c)
        $AppT($x, $x)                                               => $None,  # (x x)
        $AppT($x, $y)                                               => $None,  # (x y)
        $AppT($LamT($x, $y), $x)                                    => $Some($y),                       # a redex
            # ((λx.y) x) -> y
        $AppT($LamT($x, $AppT($AppT($z, $x), $y)), $c)              => $Some($AppT($AppT($z, $c), $y)), # a redex
            # ((λx.z x y) "c") -> (z "c" y)
        $AppT($AppT($LamT($y, $AppT($x, $y)), $y), $z)              => $Some($AppT($AppT($x, $y), $z)), # not a redex but reducible
            # (((λy.x y) y) z) -> (x y z)
        $AppT($y, $AppT($LamT($y, $AppT($x, $y)), $z))              => $Some($AppT($y, $AppT($x, $z))), # not a redex but reducible
            # (y ((λy.x y) z)) -> (y (x z))
        $AppT($AppT($LamT($x, $y), $x), $AppT($LamT($y, $x), $y))   => $Some($AppT($y, $x)),            # not a redex but contractible (twice)
            # (((λx.y) x) ((λy.x) y))  ->  (y x)
        $LamT($x, $AppT($AppT($LamT($y, $AppT($z, $y)), $x), $x))   => $Some($LamT($x, $AppT($AppT($z, $x), $x))),  # not a redex but reducible
            # (λx.(λy.z y) x x) -> (λx.z x x)        # TODO: use as example for beta-eta reduction

        $omegaX                                                     => $None,               # (λx.x x)
        $OmegaXX                                                    => $None,               # ((λx.x x) (λx.x x))   # a redex, contracting to itself
        $omegaY                                                     => $None,               # (λy.y y)
        $OmegaYY                                                    => $None,               # ((λy.y y) (λy.y y))   # a redex, contracting to itself
        $OmegaXY                                                    => $Some($OmegaYY),     # ((λx.x x) (λy.y y))   # a redex, contracting to itself (module alpha-conv)
        
        $AppT($LamT($x, $AppT($x, $x)), $yz)                        => $Some($AppT($yz, $yz)),  # ((λx.(x x)) (y z)) # only "half of" Omega
    );
}


{ #alpha-problematic-vars
    is_properLambdaFn($alpha-problematic-vars, 'alpha-problematic-vars');

    my $arg  = $AppT($AppT($AppT($x, $y), $z), $AppT($u, $v));  # (x y z (u v))
    my $lamX = $LamT($x, $AppT($AppT($z, $y), $x));             # λx.z y x
    my $lamZ = $LamT($z, $lamX);                                # λz.λx.z y x
    my $func = $LamT($y, $lamZ);                                # λy.λz.λx.z y x
    my $app  = $AppT($func, $arg);                              # (λy.λz.λx.z y x) (x y z (u v))
    my $lam  = $LamT($x, $app);                                 # λx.((λy.λz.λx.z y x) (x y z (u v)))

    my ($t, $apvs);

    $t = $x;    # not a beta-redex
    $apvs = $alpha-problematic-vars($t);
    $has_length($apvs, 0, "(alpha-problematic-vars '{$Term2source($t)})");

    $t = $c;    # not a beta-redex
    $apvs = $alpha-problematic-vars($t);
    $has_length($apvs, 0, "(alpha-problematic-vars '{$Term2source($t)})");

    $t = $arg;  # an AppT but not beta-reducible
    $apvs = $alpha-problematic-vars($t);
    $has_length($apvs, 0, "(alpha-problematic-vars '{$Term2source($t)})");

    $t = $lam;
    $apvs = $alpha-problematic-vars($t);    # not a beta-redex
    $has_length($apvs, 0, "(alpha-problematic-vars '{$Term2source($t)})");

    $t = $app;
    $apvs = $alpha-problematic-vars($t);
    # only x and z because 
    #   a) y is the substitution var (hence not free under a binder y) 
    #   b) there are no binders u and v (in the body of func)
    $has_length($apvs, 2,    "(alpha-problematic-vars '{$Term2source($t)})");
    $contains_ok($x, $apvs,  "(alpha-problematic-vars '{$Term2source($t)})");
    $contains_ok($z, $apvs,  "(alpha-problematic-vars '{$Term2source($t)})");

    #$t = $betaReduce($app);
    #diag $Term2source($t);
}


{ #alpha-needy-terms
    is_properLambdaFn($alpha-needy-terms, 'alpha-needy-terms');

    my $arg  = $AppT($AppT($AppT($x, $y), $z), $AppT($u, $v));  # (x y z (u v))
    my $lamX = $LamT($x, $AppT($AppT($z, $y), $x));             # λx.z y x
    my $lamZ = $LamT($z, $lamX);                                # λz.λx.z y x
    my $func = $LamT($y, $lamZ);                                # λy.λz.λx.z y x
    my $app  = $AppT($func, $arg);                              # ((λy.λz.λx.z y x) (x y z (u v)))
    my $lam  = $LamT($x, $app);                                 # λx.x ((λy.λz.λx.z y x) (x y z (u v)))

    my $apvs = $alpha-problematic-vars($app);
    my $apvsStr = $foldl(-> $acc, $v { $acc ~ ' ' ~ $Term2source($v) }, '[', $apvs) ~ ' ]';
    my ($t, $ants);

    $t = $x;
    $ants = $alpha-needy-terms($t, $apvs);
    $has_length($ants, 0, "(alpha-needy-terms '{$Term2source($t)} $apvsStr)");

    $t = $c;
    $ants = $alpha-needy-terms($t, $apvs);
    $has_length($ants, 0, "(alpha-needy-terms '{$Term2source($t)} $apvsStr)");

    $t = $arg;
    $ants = $alpha-needy-terms($t, $apvs);
    $has_length($ants, 0, "(alpha-needy-terms '{$Term2source($t)} $apvsStr)");

    $t = $func;
    $ants = $alpha-needy-terms($t, $apvs);
    $has_length($ants,  2,      "(alpha-needy-terms '{$Term2source($t)} $apvsStr)");
    $contains_ok($lamX, $ants,  "(alpha-needy-terms '{$Term2source($t)} $apvsStr)");
    $contains_ok($lamZ, $ants,  "(alpha-needy-terms '{$Term2source($t)} $apvsStr)");

    $t = $app;
    $ants = $alpha-needy-terms($t, $apvs);
    $has_length($ants,  2,      "(alpha-needy-terms '{$Term2source($t)} $apvsStr)");
    $contains_ok($lamX, $ants,  "(alpha-needy-terms '{$Term2source($t)} $apvsStr)");
    $contains_ok($lamZ, $ants,  "(alpha-needy-terms '{$Term2source($t)} $apvsStr)");

    $t = $lam;
    $ants = $alpha-needy-terms($t, $apvs);
    $has_length($ants,  3,      "(alpha-needy-terms '{$Term2source($t)} $apvsStr)");
    $contains_ok($lamX, $ants,  "(alpha-needy-terms '{$Term2source($t)} $apvsStr)");
    $contains_ok($lamZ, $ants,  "(alpha-needy-terms '{$Term2source($t)} $apvsStr)");
    $contains_ok($lam , $ants,  "(alpha-needy-terms '{$Term2source($t)} $apvsStr)");
}

diag curryStats;
