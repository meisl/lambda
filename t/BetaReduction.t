use v6;

use Test;
use Test::Util;

use Lambda::Boolean;
use Lambda::MaybeADT;
use Lambda::TermADT;
use Lambda::BetaReduction;

use Lambda::Conversion::Bool-conv;
use Lambda::LambdaGrammar;
use Lambda::LambdaModel;


plan 84;

sub test(Term:D $t, Str:D $desc, &tests) {
    #subtest {
     #   plan *;
        &tests("$t: $desc", $t)
    #}, $desc;
}


my $x = VarT.new(:name('x'));
my $y = VarT.new(:name('y'));
my $z = VarT.new(:name('z'));
my $c = ConstT.new(:value('c'));

# [O|o]mega: Omega (with capital O) is a (the) lambda term that beta-contracts to itself (modulo alpha-conversion).
my $omegaX = convertToP6Term( $LamT($x, $AppT($x, $x)) );  # (λx.x x)
my $OmegaXX = convertToP6Term( $AppT($omegaX, $omegaX) );  # ((λx.x x) (λx.x x))


{ # predicate betaRedex?
    is_properLambdaFn($is-betaRedex);

    is $is-betaRedex.symbol, 'betaRedex?', '$is-betaRedex.symbol';
    is $is-betaRedex.Str,    'betaRedex?', '$is-betaRedex.Str';

    my sub is_betaRedex(*@tests) {
        for @tests -> $test {
            my $term       = $test.key;
            my $termStr    = $Term2source($term);
            my $expected   = $test.value;
            my $expectedP6 = convertTBool2P6Bool($expected);
            my $desc       = $expectedP6
                                ?? "$termStr IS a beta redex" 
                                !! "$termStr is not a beta redex";
            subtest({
                cmp_ok($is-betaRedex($term), '===', $expected, $desc);
                
                my $termP6 = convertToP6Term($term);
                cmp_ok($termP6.isBetaRedex, '===', $expectedP6, $desc);
            }, $desc);
        }
    }

    is_betaRedex(
        $x                                                          => $false,  # x
        $c                                                          => $false,  # "c"
        $LamT($x, $c)                                               => $false,  # λx."c"
        $LamT($x, $x)                                               => $false,  # λx.x
        $LamT($x, $AppT($x, $c))                                    => $false,  # λx.x "c"
        $LamT($x, $AppT($x, $y))                                    => $false,  # λx.x y
        $LamT($x, $AppT($y, $x))                                    => $false,  # λx.y x
        $LamT($x, $AppT($x, $AppT($LamT($y, $LamT($z, $AppT($y, $x))), $LamT($y, $AppT($x, $y)))))  
            => $false,  # λx.x ((λy.λz.y x) (λy.x y)) # not a redex but reducible
        $AppT($x, $c)                                               => $false,  # (x c)
        $AppT($x, $x)                                               => $false,  # (x x)
        $AppT($x, $y)                                               => $false,  # (x y)
        $AppT($LamT($x, $y), $x)                                    => $true,   # ((λx.y) x)                # a redex
        $AppT($LamT($x, $AppT($AppT($z, $x), $y)), $c)              => $true,   # ((λx.z x y) "c")          # a redex
        $AppT($AppT($LamT($y, $AppT($x, $y)), $y), $z)              => $false,  # (((λy.x y) y) z)          # not a redex but reducible
        $AppT($y, $AppT($LamT($y, $AppT($x, $y)), $z))              => $false,  # (y ((λy.x y) z))          # not a redex but reducible
        $AppT($LamT($y, $AppT($x, $y)), $z)                         => $true,   # ((λy.x y) z)              # a redex
        $AppT($AppT($LamT($x, $y), $x), $AppT($LamT($y, $x), $y))   => $false,  # (((λx.y) x) ((λy.x) y))   # not a redex but reducible
        $LamT($x, $AppT($AppT($LamT($y, $AppT($z, $y)), $x), $x))   => $false,  # (λx.(λy.z y) x x)         # not a redex but reducible
        $omegaX                                                     => $false,  # (λx.x x)
        $OmegaXX                                                    => $true,   # ((λx.x x) (λx.x x))       # a redex, contracting to itself
    );
}

{ # predicate betaReducible?
    is_properLambdaFn($is-betaReducible);

    is $is-betaReducible.symbol, 'betaReducible?', '$is-betaReducible.symbol';
    is $is-betaReducible.Str,    'betaReducible?', '$is-betaReducible.Str';

    my sub is_betaReducible(*@tests) {
        for @tests -> $test {
            my $term       = $test.key;
            my $termStr    = $Term2source($term);
            my $expected   = $test.value;
            my $expectedP6 = convertTBool2P6Bool($expected);
            my $desc       = $expectedP6
                                ?? "$termStr IS beta-reducible"
                                !! "$termStr is not beta-reducible";
            subtest({
                cmp_ok($is-betaReducible($term), '===', $expected, $desc);
                
                my $termP6 = convertToP6Term($term);
                cmp_ok($termP6.isBetaReducible, '===', $expectedP6, $desc);
            }, $desc);
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
        $LamT($x, $AppT($x, $AppT($LamT($y, $LamT($z, $AppT($y, $x))), $LamT($y, $AppT($x, $y)))))  
            => $true,  # λx.x ((λy.λz.y x) (λy.x y)) # not a redex but reducible
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
    );

}


{ # function betaContract
    is_properLambdaFn($betaContract);

    is $betaContract.symbol, 'betaContract', '$betaContract.symbol';
    is $betaContract.Str,    'betaContract', '$betaContract.Str';

    my sub betaContractsTo(*@tests) {
        for @tests -> $test {
            my $term       = $test.key;
            my $termStr    = $Term2source($term);
            my $expected   = $test.value;
            my $toItself = $expected === $None;
            my $expStr  = $toItself
                ?? "itself"
                !! '(Some ' ~ $Term2source($Some2value($expected)) ~ ')';
            my $desc = "$termStr beta-contracts to $expStr";

            subtest({
                my $actual = $betaContract($term);
                is($actual, $expected, $desc)
                    or diag($actual.perl) and die;
                
                my $termP6 = convertToP6Term($term);

                my $expectedP6 = $toItself
                    ?? $termP6
                    !! convertToP6Term($Some2value($expected));

                is($termP6.beta-contract, $expectedP6, $desc);
            }, $desc);
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
        $LamT($x, $AppT($x, $AppT($LamT($y, $LamT($z, $AppT($y, $x))), $LamT($y, $AppT($x, $y)))))   # not a redex but reducible
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

        $LamT($x, $AppT($AppT($LamT($y, $AppT($z, $y)), $x), $x))   => $Some($LamT($x, $AppT($AppT($z, $x), $x))),   # not a redex but reducible
            # (λx.(λy.z y) x x) .-> (λx.z x x)
        $omegaX                                                     => $None,   # (λx.x x)
       # $OmegaXX                                                    => $None,   # ((λx.x x) (λx.x x)) # a redex, contracting to itself
       # TODO: return None for beta-contraction of Omega
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
}


{
    my ($t, $desc);

    test $x, "a VarT", {
        my $erd = $^t.beta-reduce;
        cmp_ok($erd, '===', $^t, "$^desc beta-reduces to itself");
    };

     { # c
        test $c, "a ConstT", {
            my $erd = $^t.beta-reduce;
            cmp_ok($erd, '===', $^t, "$^desc beta-reduces to itself");
        };
    }

     { # (λx.c)
        test LamT.new(:var($x), :body($c)), "a LamT with body a ConstT", {
            my $erd = $^t.beta-reduce;
            cmp_ok($erd, '===', $^t, "$^desc beta-reduces to itself");
        };
    }

    test parseLambda('(λx.x)'), "a LamT with body a VarT", {
        my $erd = $^t.beta-reduce;
        cmp_ok($erd, '===', $^t, "$^desc beta-reduces to itself");
    };
    
    { # (λx.x c)
        test LamT.new(:var($x), :body(AppT.new(:func($x), :arg($c)))), 
            "a LamT with body an AppT where arg is a ConstT", {
            my $erd = $^t.beta-reduce;
            cmp_ok($erd, '===', $^t, "$^desc beta-reduces to itself");
        };
    }

    test parseLambda('(λx.x y)'), "a LamT with body an AppT where arg is a VarT other than the lambda's", {
        my $erd = $^t.beta-reduce;
        cmp_ok($erd, '===', $^t, "$^desc beta-reduces to itself");
    };

    test parseLambda('(λx.y x)'), "a LamT with body an AppT where arg is a VarT equal to the lambda's", {
        my $erd = $^t.beta-reduce;
        cmp_ok($erd, '===', $^t, "$^desc beta-reduces to itself");
    };

    test parseLambda('(λx.x x)'), "a LamT with body an AppT where arg is a VarT equal to the lambda's but free the AppT's func", {
        my $erd = $^t.beta-reduce;
        cmp_ok($erd, '===', $^t, "$^desc beta-reduces to itself");
    };

    test parseLambda('(λx.x ((λy.λz.y x) (λy.x y)))'), "a LamT with body an AppT where func is a VarT and arg is a beta-redex", {
        my $erd = $^t.beta-reduce;
        cmp_ok($erd, 'eq', parseLambda('λx.x λz.x x'), "$^desc beta-reduces in two steps");
    };

    { # (x c)
        test AppT.new(:func($x), :arg($c)), "an AppT (arg:ConstT)", {
            my $erd = $^t.beta-reduce;
            cmp_ok($erd, '===', $^t, "$^desc beta-reduces to itself");
        };
    }

    # (x y) [40...]
    test parseLambda('(x y)'), "an AppT (func:VarT, arg:VarT)", {
        my $erd = $^t.beta-reduce;
        cmp_ok($erd, '===', $^t, "$^desc beta-reduces to itself");
    };

    # ((λy.x y) y) z [44...]
    test parseLambda('((λy.x y) y) z'), "an AppT with a beta-redex as func", {
        my $erd = $^t.beta-reduce;
        cmp_ok($erd, 'eq', parseLambda('(x y) z'), "$^desc beta-reduces to the func's beta-reduction");
    };
    
    # y ((λy.x y) z) [48...]
    test parseLambda('y ((λy.x y) z)'), "an AppT with a beta-redex as arg", {
        my $erd = $^t.beta-reduce;
        cmp_ok($erd, 'eq', parseLambda('y (x z)'), "$^desc beta-reduces to the arg's beta-reduction");
    };

    
    # (λx.((λy.z y) x) x) [57...]
    test parseLambda('(λx.((λy.z y) x) x)'), "a LamT with body an AppT where func is a beta-redex and arg a VarT", {
        my $bcd = $^t.beta-contract;
        is($bcd.isBetaReducible,  False, "$^desc beta-contracts to a non-beta-reducible term");

        cmp_ok($bcd, 'eq', parseLambda('λx.(z x) x'), "$^desc beta-contracts the inner lambda");
        # TODO: use as example for beta-eta reduction
    };

    # ((λx.y) x) ((λy.x) y) [52...]
    test parseLambda('((λx.y) x) ((λy.x) y)'), "an AppT with both, func and arg beta-redexes", {
        my $erd = $^t.beta-reduce;
        cmp_ok($erd, 'eq', parseLambda('y x'), "$^desc beta-reduces to the func's and arg's beta-reduction, resp.");
    };

}

# [O|o]mega: Omega (with capital O) is a (the) lambda term that beta-contracts to itself (modulo alpha-conversion).
skip {
    my $OmegaXX-contracted-once = $OmegaXX.beta-contract;

    cmp_ok($OmegaXX-contracted-once, '===', $OmegaXX,
        "beta-contracting '$OmegaXX' should yield same instance after 1st step");

    my $omegaY = parseLambda('λy.y y');
    my $OmegaYY = AppT.new(:func($omegaY), :arg($omegaY));
    my $OmegaXY = AppT.new(:func($omegaX), :arg($omegaY));
    my $OmegaXY-contracted-once = $OmegaXY.beta-contract;
    my $OmegaXY-contracted-twice = $OmegaXY-contracted-once.beta-contract;

    cmp_ok($OmegaXY-contracted-twice, '===', $OmegaXY-contracted-once,
        "beta-contracting '$OmegaXY' should yield same instance after 2nd step");

    is($OmegaXX.beta-reduce, $OmegaXX, "beta-reduce should terminate for $OmegaXX");
    is($OmegaXY.beta-reduce, $OmegaYY, "beta-reduce should terminate for $OmegaXY");
}

# examples requiring alpha-conversion before substitution:
if False {

    test parseLambda('λx.x ((λy.λz.y x) (x y z))'), "a LamT with body an AppT where arg is a beta-redex", {
        is($^t.isBetaRedex,      False, "$^desc is not itself a beta redex");
        is($^t.isBetaReducible,  True,  "$^desc is itself beta-reducible");
        my $bcd = $^t.beta-contract;
        cmp_ok($bcd, 'eq', parseLambda('λx.x x'), "$^desc beta-contracts the AppT's arg");
        my $brd = $^t.beta-reduce;
        cmp_ok($brd, 'eq', parseLambda('λx.x x'), "$^desc beta-reduces to the AppT's arg");
    };

}
