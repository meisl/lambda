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


plan 116;

sub test(Term:D $t, Str:D $desc, &tests) {
    #subtest {
     #   plan *;
        &tests("$t: $desc", $t)
    #}, $desc;
}


my $u = VarT.new(:name('u'));
my $v = VarT.new(:name('v'));
my $x = VarT.new(:name('x'));
my $y = VarT.new(:name('y'));
my $z = VarT.new(:name('z'));
my $c = ConstT.new(:value('c'));

# [O|o]mega: Omega (with capital O) is a (the) lambda term that beta-contracts to itself (modulo alpha-conversion).
my $omegaX  = convertToP6Term( $LamT($x, $AppT($x, $x)) );  # (λx.x x)
my $OmegaXX = convertToP6Term( $AppT($omegaX, $omegaX) );   # ((λx.x x) (λx.x x))
my $omegaY  = convertToP6Term( $LamT($y, $AppT($y, $y)) );  # (λy.y y)
my $OmegaYY = convertToP6Term( $AppT($omegaY, $omegaY) );   # ((λy.y y) (λy.y y))
my $OmegaXY = convertToP6Term( $AppT($omegaX, $omegaY) );   # ((λx.x x) (λy.y y))


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
        $LamT($x, $AppT($x, $AppT($LamT($y, $LamT($z, $AppT($y, $x))), $LamT($y, $AppT($x, $y)))))          # not a redex but contractible (twice)
            => $false,  # λx.x ((λy.λz.y x) (λy.x y))
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
        $omegaY                                                     => $false,  # (λy.y y)
        $OmegaYY                                                    => $true,   # ((λy.y y) (λy.y y))       # a redex, contracting to itself
        $OmegaXY                                                    => $true,   # ((λx.x x) (λy.y y))       # a redex, contracting to itself (module alpha-conv)
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
    );

}


{ # function betaContract
    is_properLambdaFn($betaContract);

    is $betaContract.symbol, 'betaContract', '$betaContract.symbol';
    is $betaContract.Str,    'betaContract', '$betaContract.Str';

    my sub betaContractsTo(*@tests) {
        for @tests -> $test {
            my $term     = $test.key;
            my $termStr  = $Term2source($term);
            my $expected = $test.value;
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


{ # function betaReduce
    is_properLambdaFn($betaReduce);

    is $betaReduce.symbol, 'betaReduce', '$betaReduce.symbol';
    is $betaReduce.Str,    'betaReduce', '$betaReduce.Str';

    my sub betaReducesTo(*@tests) {
        for @tests -> $test {
            my $term     = $test.key;
            my $termStr  = $Term2source($term);
            my $expected = $test.value;
            my $toItself = $expected === $None;
            my $expStr = $toItself
                ?? "itself"
                !! '(Some ' ~ $Term2source($Some2value($expected)) ~ ')';
            my $desc = "$termStr beta-reduces to $expStr";

            subtest({
                my $actual = $betaReduce($term);
                is($actual, $expected, $desc)
                    or diag($actual.perl) and die;
                
                my $termP6 = convertToP6Term($term);

                my $expectedP6 = $toItself
                    ?? $termP6
                    !! convertToP6Term($Some2value($expected));

                is($termP6.beta-reduce, $expectedP6, $desc);
            }, $desc);
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
    );
}


# [O|o]mega: Omega (with capital O) is a (the) lambda term that beta-contracts to itself (modulo alpha-conversion).
{
    my $OmegaXX-contracted-once = $OmegaXX.beta-contract;

    cmp_ok($OmegaXX-contracted-once, '===', $OmegaXX,
        "beta-contracting '$OmegaXX' should yield same instance after 1st step");

    my $OmegaXY-contracted-once = $OmegaXY.beta-contract;
    my $OmegaXY-contracted-twice = $OmegaXY-contracted-once.beta-contract;

    cmp_ok($OmegaXY-contracted-twice, '===', $OmegaXY-contracted-once,
        "beta-contracting '$OmegaXY' should yield same instance after 2nd step");

    is($OmegaXX.beta-reduce, $OmegaXX, "beta-reduce should terminate for $OmegaXX");
    is($OmegaXY.beta-reduce, $OmegaYY, "beta-reduce should terminate for $OmegaXY");
}


{ #alpha-problematic-vars
    is_properLambdaFn($alpha-problematic-vars);

    is $alpha-problematic-vars.symbol, 'alpha-problematic-vars', '$alpha-problematic-vars.symbol';
    is $alpha-problematic-vars.Str,    'alpha-problematic-vars', '$alpha-problematic-vars.Str';

    my $arg  = $AppT($AppT($AppT($x, $y), $z), $AppT($u, $v));              # (x y z (u v))
    my $func = $LamT($y, $LamT($z, $LamT($x, $AppT($AppT($z, $y), $x))));   # λy.λz.λx.z y x
    my $app  = $AppT($func, $arg);                                          # ((λy.λz.λx.z y x) (x y z (u v)))
    my $lam  = $LamT($x, $app);                                             # λx.x ((λy.λz.λx.z y x) (x y z (u v)))

    my ($t, $apvs);

    $t = $x;
    $apvs = $alpha-problematic-vars($t);
    $has_length($apvs, 0, "(alpha-problematic-vars '{$Term2source($t)})");

    $t = $c;
    $apvs = $alpha-problematic-vars($t);
    $has_length($apvs, 0, "(alpha-problematic-vars '{$Term2source($t)})");

    $t = $arg;  # an AppT but not beta-reducible
    $apvs = $alpha-problematic-vars($t);
    $has_length($apvs, 0, "(alpha-problematic-vars '{$Term2source($t)})");

    $t = $lam;
    $apvs = $alpha-problematic-vars($t);
    $has_length($apvs, 0, "(alpha-problematic-vars '{$Term2source($t)})");

    $t = $app;
    $apvs = $alpha-problematic-vars($t);
    # only x and z because 
    #   a) y is the substitution var (hence not free under a binder y) 
    #   b) there are no binders u and v (in the body of func)
    $has_length($apvs, 2,    "(alpha-problematic-vars '{$Term2source($t)})");
    $contains_ok($x, $apvs,  "(alpha-problematic-vars '{$Term2source($t)})");
    $contains_ok($z, $apvs,  "(alpha-problematic-vars '{$Term2source($t)})");
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
