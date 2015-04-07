use v6;
use Test;
use Test::Util;
use Test::Util_Lambda;
use Test::Util_Term;
use Test::Util_List;

use Lambda::Boolean;
use Lambda::PairADT;
use Lambda::MaybeADT;
use Lambda::ListADT;
use Lambda::TermADT;

use Lambda::Conversion;

use Lambda::P6Currying;

# module under test:
use Lambda::BetaReduction;

plan 134;


{ # collect-then-apply-args
    is_properLambdaFn $collect-then-apply-args, 'collect-then-apply-args';

    testTermFn($collect-then-apply-args, :expectedToStr(&lambdaArgToStr),
        [`'a', [],             `'x']               => $None,
        [`'a', [`'b'],         `'x']               => $None,
        [`'a', [],             `'"c"']             => $None,
        [`'a', [`'b'],         `'"c"']             => $None,
        [`'a', [],             `'(x (λy.x y))']    => $None,
        [`'a', [`'b'],         `'(x (λy.x y))']    => $None,
        [`'a', [],             `'("c" (λy.x y))']  => $None,
        [`'a', [`'b'],         `'("c" (λy.x y))']  => $None,
        [`'a', [],             `'λy.x y']          => $Some(`'x a' => []),
        [`'a', [`'b'],         `'λy.x y']          => $Some(`'x a' => [`'b']),

        [`'a', [],             `'(λx.λy.x) (x y)'] => $Some(`'x y' => []),
        [`'a', [`'b'],         `'(λx.λy.x) (x y)'] => $Some(`'x y' => [`'b']),

        [`'a', [`'b',`'g'],         `'(λf1.λf2.λ_.λh.h f1 f2)']         => $Some(`'λh.h a b' => []),
        [`'a', [`'b',`'g', `'h'],   `'(λf1.λf2.λ_.λh.h f1 f2)']         => $Some(`'h a b'    => []),
        [`'b', [`'g'],              `'(λf1.λf2.λ_.λh.h f1 f2) a']       => $Some(`'λh.h a b' => []),
        [`'b', [`'g', `'h'],        `'(λf1.λf2.λ_.λh.h f1 f2) a']       => $Some(`'h a b'    => []),
        [`'g', [],                  `'(λf1.λf2.λ_.λh.h f1 f2) a b']     => $Some(`'λh.h a b' => []),
        [`'g', [`'h'],              `'(λf1.λf2.λ_.λh.h f1 f2) a b']     => $Some(`'h a b'    => []),
        [`'h', [],                  `'(λf1.λf2.λ_.λh.h f1 f2) a b g']   => $Some(`'h a b'    => []),
        [`'h', [`'k'],              `'(λf1.λf2.λ_.λh.h f1 f2) a b g']   => $Some(`'h a b'    => [`'k']),
    );
}


{ # apply-args

    my sub test_variant_apply-args($fut) {
        testTermFn($fut, :expectedToStr(&lambdaArgToStr),
            [[],            [],             `'x']       => ($None       => []),
            [[z => `'y'],   [],             `'x']       => ($None       => []),
            [[x => `'y'],   [],             `'x']       => ($Some(`'y') => []),
            [[],            [`'a', `'b'],   `'x']       => ($None       => [`'a', `'b']),
            [[z => `'y'],   [`'a', `'b'],   `'x']       => ($None       => [`'a', `'b']),
            [[x => `'y'],   [`'a', `'b'],   `'x']       => ($Some(`'y') => [`'a', `'b']),

            [[],            [],             `'"c"']     => ($None => []),
            [[z => `'y'],   [],             `'"c"']     => ($None => []),
            [[x => `'y'],   [],             `'"c"']     => ($None => []),
            [[],            [`'a', `'b'],   `'"c"']     => ($None => [`'a', `'b']),
            [[z => `'y'],   [`'a', `'b'],   `'"c"']     => ($None => [`'a', `'b']),
            [[x => `'y'],   [`'a', `'b'],   `'"c"']     => ($None => [`'a', `'b']),

            [[],            [],             `'λx.y x']  => ($None               => []),
            [[x => `'y'],   [],             `'λx.y x']  => ($None               => []),
            [[y => `'z'],   [],             `'λx.y x']  => ($Some(`'λx.z x')    => []),
            #[[y => `'x'],   [],             `'λx.y x']  => ($Some(`'λα1.x α1')  => []), # requires alpha-conversion
            [[],            [`'a', `'b'],   `'λx.y x']  => ($Some(`'y a')       => [`'b']),
            [[],            [`'a', `'b'],   `'λx.y z']  => ($Some(`'y z')       => [`'b']),
            [[x => `'y'],   [`'a', `'b'],   `'λx.y x']  => ($Some(`'y a')       => [`'b']),
            [[y => `'z'],   [`'a', `'b'],   `'λx.y x']  => ($Some(`'z a')       => [`'b']),
            [[y => `'x'],   [`'a', `'b'],   `'λx.y x']  => ($Some(`'x a')       => [`'b']),

            [[],            [],                 `'λx.λy.x y z']   => ($None                     => []),
            [[z => `'u'],   [],                 `'λx.λy.x y z']   => ($Some(`'λx.λy.x y u')     => []),
            #[[z => `'y'],   [],                 `'λx.λy.x y z']   => ($Some(`'λx.λα1.x α1 y')   => []), # requires alpha-conversion
            [[],                        [`'a'],             `'λx.λy.x y z']   => ($Some(`'λy.a y z')        => []),
            [[z => `'u'],               [`'a'],             `'λx.λy.x y z']   => ($Some(`'λy.a y u')        => []),
            [[z => `'u', y => `'v'],    [`'a'],             `'λx.λy.x y z']   => ($Some(`'λy.a y u')        => []),     # one more subst (unapplicable)
            #[[z => `'y'],   [`'a'],             `'λx.λy.x y z']   => ($Some(`'λα2.a α2 y')      => []), # requires alpha-conversion
            [[],            [`'a', `'b'],       `'λx.λy.x y z']   => ($Some(`'a b z')           => []),
            [[z => `'u'],   [`'a', `'b'],       `'λx.λy.x y z']   => ($Some(`'a b u')           => []),
            [[z => `'y'],   [`'a', `'b'],       `'λx.λy.x y z']   => ($Some(`'a b y')           => []),
            [[],            [`'a', `'b', `'c'], `'λx.λy.x y z']   => ($Some(`'a b z')           => [`'c']),
            [[z => `'u'],   [`'a', `'b', `'c'], `'λx.λy.x y z']   => ($Some(`'a b u')           => [`'c']),
            [[z => `'y'],   [`'a', `'b', `'c'], `'λx.λy.x y z']   => ($Some(`'a b y')           => [`'c']),
        );
    }

    is_properLambdaFn $apply-args, 'apply-args';
    test_variant_apply-args($apply-args);

    is_properLambdaFn $apply-args_special, 'apply-args_special';
    test_variant_apply-args(
        -> $substitutions, $rest-args, $inTerm {
            case-Term($inTerm,
                ConstT => -> Mu     { $apply-args($substitutions, $rest-args, $inTerm) },
                VarT   => -> Mu     { $apply-args($substitutions, $rest-args, $inTerm) },
                AppT   => -> Mu, Mu { $apply-args($substitutions, $rest-args, $inTerm) },
                LamT   => -> $v, $b {
                    case-List($rest-args, 
                        nil => { $apply-args($substitutions, $rest-args, $inTerm) },
                        cons => -> $a, $as {
                            my $out = $apply-args_special($substitutions, $a, $as, $v, $b);
                            my $t = $fst($out);
                            _if_($Term-eq($t, $inTerm),
                                { $Pair($None, $snd($out)) },
                                { $Pair($Some($t), $snd($out)) }
                            )
                        }
                    )
                }
            )
        }
    );
}


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
        `'x'                                        => $false,
        `'"c"'                                      => $false,
        `'λx."c"'                                   => $false,
        `'λx.x'                                     => $false,
        `'λx.x "c"'                                 => $false,
        `'λx.x y'                                   => $false,
        `'λx.y x'                                   => $false,
        $LamT('x', $AppT(`'x', $AppT(`'λy.λz.y x', `'λy.x y')))          # not a redex but contractible (twice)
            => $false,  # λx.x ((λy.λz.y x) (λy.x y))
        `'x "c"'                                    => $false,
        `'x x'                                      => $false,
        `'x y'                                      => $false,
        `'(λx.y) x'                                 => $true,   # a redex
        $AppT(`'λx.z x y', `'"c"')                  => $true,   # ((λx.z x y) "c")          # a redex
        $AppT(`'(λy.x y) y', `'z')                  => $false,  # (((λy.x y) y) z)          # not a redex but reducible
        $AppT(`'y', `'(λy.x y) z')                  => $false,  # (y ((λy.x y) z))          # not a redex but reducible
        `'(λy.x y) z'                               => $true,   # ((λy.x y) z)              # a redex
        $AppT(`'(λx.y) x', `'(λy.x) y')             => $false,  # (((λx.y) x) ((λy.x) y))   # not a redex but reducible
        $LamT('x', $AppT(`'(λy.z y) x', `'x'))      => $false,  # (λx.(λy.z y) x x)         # not a redex but reducible
        
        `'(λx.x x)'                                 => $false,  # omegaX
        `'(λx.x x) (λx.x x)'                        => $true,   # OmegaXX: a redex, contracting to itself
        `'(λy.y y)'                                 => $false,  # omegaY
        `'(λy.y y) (λy.y y)'                        => $true,   # OmegaYY: a redex, contracting to itself
        `'(λx.x x) (λy.y y)'                        => $true,   # OmegaXY: a redex, contracting to itself (module alpha-conv)
        
        `'(λx.x x) (y z)'                           => $true,   # only "half of" Omega
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
        `'x'                                        => $false,
        `'"c"'                                      => $false,
        `'λx."c"'                                   => $false,
        `'λx.x'                                     => $false,
        `'λx.x "c"'                                 => $false,
        `'λx.x y'                                   => $false,
        `'λx.y x'                                   => $false,
        $LamT('x', $AppT(`'x', $AppT(`'λy.λz.y x', `'λy.x y')))          # not a redex but contractible (twice)
            => $true,  # λx.x ((λy.λz.y x) (λy.x y))
        `'x "c"'                                    => $false,
        `'x x'                                      => $false,
        `'x y'                                      => $false,
        `'(λx.y) x'                                 => $true,   # a redex
        $AppT(`'λx.z x y', `'"c"')                  => $true,   # ((λx.z x y) "c")          # a redex
        $AppT(`'(λy.x y) y', `'z')                  => $true,   # (((λy.x y) y) z)          # not a redex but reducible
        $AppT(`'y', `'(λy.x y) z')                  => $true,   # (y ((λy.x y) z))          # not a redex but reducible
        `'(λy.x y) z'                               => $true,   # ((λy.x y) z)              # a redex
        $AppT(`'(λx.y) x', `'(λy.x) y')             => $true,   # (((λx.y) x) ((λy.x) y))   # not a redex but reducible
        $LamT('x', $AppT(`'(λy.z y) x', `'x'))      => $true,   # (λx.(λy.z y) x x)         # not a redex but reducible
        
        `'(λx.x x)'                                 => $false,  # omegaX
        `'(λx.x x) (λx.x x)'                        => $true,   # OmegaXX: a redex, contracting to itself
        `'(λy.y y)'                                 => $false,  # omegaY
        `'(λy.y y) (λy.y y)'                        => $true,   # OmegaYY: a redex, contracting to itself
        `'(λx.x x) (λy.y y)'                        => $true,   # OmegaXY: a redex, contracting to itself (module alpha-conv)
        
        `'(λx.x x) (y z)'                           => $true,   # only "half of" Omega
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
                !! '(Some `' ~ $Term2source($Some2value($expected)) ~ ')';
            my $desc = "$termStr beta-contracts to $expStr";

            my $actual = $betaContract($term);
            is($actual, $expected, $desc)
                or diag($actual.perl) and die;
        }
    }

    # TODO: (λx.λy.x) (x y)

    # without the need for α-conversion
    betaContractsTo(
        `'x'                                    => $None,
        `'"c"'                                  => $None,
        `'λx."c"'                               => $None,
        `'λx.x'                                 => $None,
        `'λx.x "c"'                             => $None,
        `'λx.x y'                               => $None,
        `'λx.y x'                               => $None,
        $LamT('x', $AppT(`'x', $AppT(`'λy.λz.y x', `'λy.x y')))   # not a redex but contractible (twice)
            => $Some($LamT('x', $AppT(`'x', $LamT('z', `'(λy.x y) x')))),  # `'λx.x ((λy.λz.y x) (λy.x y))' -> `'λx.x (λz.(λy.x y) x)'
        `'x "c"'                                => $None,
        `'x x'                                  => $None,
        `'x y'                                  => $None,
        `'(λx.y) x'                             => $Some(`'y'),         # a redex
        $AppT(`'λx.z x y', `'"c"')              => $Some(`'z "c" y'),   # a redex
            # ((λx.z x y) "c") -> (z "c" y)
        $AppT(`'(λy.x y) y', `'z')              => $Some(`'x y z'), # not a redex but reducible
            # ((λy.x y) y z) -> (x y z)
        $AppT(`'y', `'(λy.x y) z')              => $Some(`'y (x z)'), # not a redex but reducible
            # (y ((λy.x y) z)) -> (y (x z))
        
        # see below for (((λx.y) x) ((λy.x) y))   # not a redex but contractible (twice)

        $LamT('x', $AppT(`'(λy.z y) x', `'x'))          => $Some(`'λx.z x x'),  # not a redex but reducible
            # (λx.(λy.z y) x x) -> (λx.z x x)

        `'z ((λx.x) y) b a'     => $Some(`'z y b a'), # not a redex but reducible

        `'(λx.x x)'             => $None,                           # omegaX
        `'((λx.x x) (λx.x x))'  => $None,                           # OmegaXX: a redex, contracting to itself
        `'(λy.y y)'             => $None,                           # omegaY
        `'((λy.y y) (λy.y y))'  => $None,                           # OmegaYY: a redex, contracting to itself
        `'((λx.x x) (λy.y y))'  => $Some(`'(λy.y y) (λy.y y)'),     # OmegaXY: a redex, contracting to itself (module alpha-conv)
        
        `'(λx.x x) (λy.x x)'    => $Some(`'(λy.x x) (λy.x x)'),     # not Omega (2nd binder y != x)
        `'(λy.x x) (λx.x x)'    => $Some(`'x x'),                   # not Omega (1st binder y != x)
        `'(λx.x x) (y z)'       => $Some(`'(y z) (y z)'),           # only "half of" Omega
    );

    subtest({ # with necessary α-conversion:
        my $t = `'(λx.λy.x) (x y)'; # contracts to (λα1.x y)
        my $actual = $Some2value($betaContract($t));
        my $α1 = $LamT2var($actual);
        isnt($α1, 'x', 'fresh var is different from var x');
        isnt($α1, 'y', 'fresh var is different from var y');
        my $expected = $LamT($α1, `'x y');
        is_eq-Term($actual, $LamT($α1, `'x y'), "`({$Term2srcLess($t)}) beta-contracts to `({$Term2srcLess($expected)})");
    });

    my ($t, $bcd1, $bcd2, $expectedBrd);


    $t = `'((λx.y) x) ((λy.x) y)';  # can contract twice; NO prescribed order!
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

        $expectedBrd = `'y x';
        is($bcd2, $expectedBrd,
            "beta-contracting {$Term2source($t)} should yield {$Term2source($expectedBrd)}");
    }, "{$Term2source($t)} can contract twice; NO prescribed order!");


    subtest({ # a term that β-"contracts" to an ever larger term: (λx.x x y) (λx.x x y)
        my $t = {
            my $lx-xxy  = $LamT('x', $AppT(`'x x', `'y')); # lam(<x>, <x x y>)
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
    }, 'a term that β-"contracts" to an ever larger term: (λx.x x y) (λx.x x y)');
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
                !! '(Some `' ~ $Term2source($Some2value($expected)) ~ ')';
            my $desc = "$termStr beta-reduces to $expStr";

            my $actual = $betaReduce($term);
            is($actual, $expected, $desc)
                or diag($actual.perl) ;
        }
    }


    betaReducesTo(
        `'x'                                        => $None,
        `'"c"'                                      => $None,
        `'λx."c"'                                   => $None,
        `'λx.x'                                     => $None,
        `'λx.x "c"'                                 => $None,
        `'λx.x y'                                   => $None,
        `'λx.y x'                                   => $None,
        $LamT('x', $AppT(`'x', $AppT(`'λy.λz.y x', `'λy.x y')))   # not a redex but contractible (twice)
            => $Some($LamT('x', $AppT(`'x', `'λz.x x'))),  # λx.x ((λy.λz.y x) (λy.x y)) -> λx.x (λz.x x)
        `'x "c"'                                    => $None,
        `'x x'                                      => $None,
        `'x y'                                      => $None,
        `'(λx.y) x'                                 => $Some(`'y'), # a redex
        $AppT(`'λx.z x y', `'"c"')              => $Some(`'z "c" y'),      # a redex
            # ((λx.z x y) "c") -> (z "c" y)
        $AppT(`'(λy.x y) y', `'z')               => $Some(`'x y z'),        # not a redex but reducible
            # (((λy.x y) y) z) -> (x y z)
        $AppT(`'y', `'(λy.x y) z')               => $Some(`'y (x z)'),      # not a redex but reducible
            # (y ((λy.x y) z)) -> (y (x z))
        $AppT(`'(λx.y) x', `'(λy.x) y')   => $Some(`'y x'),         # not a redex but contractible (twice)
            # (((λx.y) x) ((λy.x) y))  ->  (y x)
        $LamT('x', $AppT(`'(λy.z y) x', `'x'))   => $Some(`'λx.z x x'),    # not a redex but reducible
            # (λx.(λy.z y) x x) -> (λx.z x x)        # TODO: use as example for beta-eta reduction': λx.z x x

        `'z ((λx.x) y) b a'     => $Some(`'z y b a'), # not a redex but reducible

        `'(λx.x x)'             => $None,                           # omegaX
        `'((λx.x x) (λx.x x))'  => $None,                           # OmegaXX: a redex, contracting to itself
        `'(λy.y y)'             => $None,                           # omegaY
        `'((λy.y y) (λy.y y))'  => $None,                           # OmegaYY: a redex, contracting to itself
        `'((λx.x x) (λy.y y))'  => $Some(`'(λy.y y) (λy.y y)'),     # OmegaXY: a redex, contracting to itself (module alpha-conv)
        
        `'(λx.x x) (λy.x x)'    => $Some(`'x x'),                   # not Omega (2nd binder y != x)
        `'(λy.x x) (λx.x x)'    => $Some(`'x x'),                   # not Omega (1st binder y != x)
        `'(λx.x x) (y z)'       => $Some(`'(y z) (y z)'),           # only "half of" Omega
    );
}


{ #alpha-problematic-vars
    is_properLambdaFn($alpha-problematic-vars, 'alpha-problematic-vars');

    my $arg  = `'x y z (u v)';
    my $lamX = `'λx.z y x';
    my $lamZ = `'λz.λx.z y x';
    my $func = `'λy.λz.λx.z y x';
    my $app  = $AppT($func, $arg);                              # (λy.λz.λx.z y x) (x y z (u v))
    my $lam  = $LamT('x', $app);                                 # λx.((λy.λz.λx.z y x) (x y z (u v)))

    my ($t, $apvs);

    $t = `'x';    # not a beta-redex
    $apvs = $alpha-problematic-vars($t);
    $has_length($apvs, 0, "(alpha-problematic-vars '{$Term2source($t)})");

    $t = `'"c"';    # not a beta-redex
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
    $contains_ok(`'x', $apvs,  "(alpha-problematic-vars '{$Term2source($t)})");
    $contains_ok(`'z', $apvs,  "(alpha-problematic-vars '{$Term2source($t)})");

    my $m = $betaReduce($app);
    #diag lambdaArgToStr($m);
    $t = $Some2value($m);
    diag $Term2srcLess($app) ~ '  =_β  ' ~ $Term2srcLess($t);
    #is_eq-Term($t, ...
}


{ #alpha-needy-terms
    is_properLambdaFn($alpha-needy-terms, 'alpha-needy-terms');

    my $arg  = `'x y z (u v)';
    my $lamX = `'λx.z y x';
    my $lamZ = `'λz.λx.z y x';
    my $func = `'λy.λz.λx.z y x';
    my $app  = $AppT($func, $arg);                              # ((λy.λz.λx.z y x) (x y z (u v)))
    my $lam  = $LamT('x', $app);                                 # λx.x ((λy.λz.λx.z y x) (x y z (u v)))

    my $apvs = $alpha-problematic-vars($app);
    my $apvsStr = $foldl(-> $acc, $v { $acc ~ ' ' ~ $Term2source($v) }, '[', $apvs) ~ ' ]';
    my ($t, $ants);

    $t = `'x';
    $ants = $alpha-needy-terms($t, $apvs);
    $has_length($ants, 0, "(alpha-needy-terms '{$Term2source($t)} $apvsStr)");

    $t = `'"c"';
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
