use v6;

use Test;
use Test::Util;

use Lambda::Boolean;
use Lambda::MaybeADT;
use Lambda::TermADT;
use Lambda::EtaReduction;

use Lambda::Conversion::Bool-conv;
use Lambda::LambdaModel;

plan 80;


{ # predicate etaRedex?
    is_properLambdaFn($is-etaRedex);

    is $is-etaRedex.symbol, 'etaRedex?', '$is-etaRedex.symbol';
    is $is-etaRedex.Str,    'etaRedex?', '$is-etaRedex.Str';

    my sub is_etaRedex(*@tests) {
        for @tests -> $test {
            my $term       = $test.key;
            my $termStr    = $Term2source($term);
            my $expected   = $test.value;
            my $expectedP6 = convertTBool2P6Bool($expected);
            my $desc       = $expectedP6
                                ?? "$termStr IS an eta redex" 
                                !! "$termStr is not an eta redex";
            subtest({
                cmp_ok($is-etaRedex($term), '===', $expected, $desc);
                
                my $termP6 = convertToP6Term($term);
                cmp_ok($termP6.isEtaRedex, '===', $expectedP6, $desc);
            }, $desc);
        }
    }

    my $x = $VarT('x');
    my $y = $VarT('y');
    my $z = $VarT('z');
    my $c = $ConstT('c');

    is_etaRedex(
        $x                                                          => $false,  # x
        $c                                                          => $false,  # "c"
        $AppT($x, $c)                                               => $false,  # (x "c")
        $AppT($x, $x)                                               => $false,  # (x x)
        $AppT($x, $y)                                               => $false,  # (x y)
        $LamT($x, $c)                                               => $false,  # (λx."c")
        $LamT($x, $x)                                               => $false,  # (λx.x)
        $LamT($x, $AppT($x, $x))                                    => $false,  # (λx.x x)
        $LamT($x, $AppT($x, $c))                                    => $false,  # (λx.x "c")
        $LamT($x, $AppT($x, $y))                                    => $false,  # (λx.x y)
        $LamT($x, $AppT($y, $x))                                    => $true,   # (λx.y x)
        $LamT($x, $AppT($x, $LamT($y, $AppT($x, $y))))              => $false,  # (λx.x λy.x y)
        $AppT($LamT($y, $AppT($x, $y)), $y)                         => $false,  # ((λy.x y) y)
        $AppT($LamT($x, $AppT($y, $x)), $LamT($y, $AppT($x, $y)))   => $false,  # ((λx.y x) (λy.x y))
        $LamT($x, $AppT($LamT($y, $AppT($z, $y)), $x))              => $true,   # (λx.(λy.z y) x)
        $LamT($x, $AppT($LamT($y, $AppT($x, $y)), $x))              => $false,  # (λx.(λy.x y) x)
        $LamT($x, $AppT($LamT($x, $AppT($x, $y)), $x))              => $true,   # (λx.(λx.x y) x)
    );
}


{ # predicate etaReducible?
    is_properLambdaFn($is-etaReducible);

    is $is-etaReducible.symbol, 'etaReducible?', '$is-etaReducible.symbol';
    is $is-etaReducible.Str,    'etaReducible?', '$is-etaReducible.Str';

    my sub is_etaReducible(*@tests) {
        for @tests -> $test {
            my $term       = $test.key;
            my $termStr    = $Term2source($term);
            my $expected   = $test.value;
            my $expectedP6 = convertTBool2P6Bool($expected);
            my $desc       = $expectedP6
                                ?? "$termStr IS eta-reducible" 
                                !! "$termStr is not eta-redubible";
            subtest({
                cmp_ok($is-etaReducible($term), '===', $expected, $desc);
                
                my $termP6 = convertToP6Term($term);
                cmp_ok($termP6.isEtaReducible, '===', $expectedP6, $desc);
            }, $desc);
        }
    }

    my $x = $VarT('x');
    my $y = $VarT('y');
    my $z = $VarT('z');
    my $c = $ConstT('c');

    is_etaReducible(
        $x                                                          => $false,  # x
        $c                                                          => $false,  # "c"
        $AppT($x, $c)                                               => $false,  # (x "c")
        $AppT($x, $x)                                               => $false,  # (x x)
        $AppT($x, $y)                                               => $false,  # (x y)
        $LamT($x, $c)                                               => $false,  # (λx."c")
        $LamT($x, $x)                                               => $false,  # (λx.x)
        $LamT($x, $AppT($x, $x))                                    => $false,  # (λx.x x)
        $LamT($x, $AppT($x, $c))                                    => $false,  # (λx.x "c")
        $LamT($x, $AppT($x, $y))                                    => $false,  # (λx.x y)
        $LamT($x, $AppT($y, $x))                                    => $true,   # (λx.y x)              # a redex
        $LamT($x, $AppT($x, $LamT($y, $AppT($x, $y))))              => $true,   # (λx.x λy.x y)         # not a redex but reducible
        $AppT($LamT($y, $AppT($x, $y)), $y)                         => $true,   # ((λy.x y) y)          # not a redex but reducible
        $AppT($LamT($x, $AppT($y, $x)), $LamT($y, $AppT($x, $y)))   => $true,   # ((λx.y x) (λy.x y))   # not a redex but reducible
        $LamT($x, $AppT($LamT($y, $AppT($z, $y)), $x))              => $true,   # (λx.(λy.z y) x)       # a redex (with inner redex)
        $LamT($x, $AppT($LamT($y, $AppT($x, $y)), $x))              => $true,   # (λx.(λy.x y) x)       # not a redex but reducible
        $LamT($x, $AppT($LamT($x, $AppT($x, $y)), $x))              => $true,   # (λx.(λx.x y) x)       # a redex
    );
}


{ # function etaContract
    is_properLambdaFn($etaContract);

    is $etaContract.symbol, 'etaContract', '$etaContract.symbol';
    is $etaContract.Str,    'etaContract', '$etaContract.Str';

    my sub etaContractsTo(*@tests) {
        for @tests -> $test {
            my $term       = $test.key;
            my $termStr    = $Term2source($term);
            my $expected   = $test.value;
            my $toItself = $expected === $None;
            my $expStr  = $toItself
                ?? "itself"
                !! '(Some ' ~ $Term2source($Some2value($expected)) ~ ')';
            my $desc = "$termStr eta-contracts to $expStr";

            subtest({
                my $actual = $etaContract($term);
                is($actual, $expected, $desc)
                    or diag($actual.perl) and die;
                
                my $termP6 = convertToP6Term($term);

                my $expectedP6 = $toItself
                    ?? $termP6
                    !! convertToP6Term($Some2value($expected));

                is($termP6.eta-contract, $expectedP6, $desc);
            }, $desc);
        }
    }

    my $x = $VarT('x');
    my $y = $VarT('y');
    my $z = $VarT('z');
    my $c = $ConstT('c');

    etaContractsTo(
        $x                                              => $None,    # x
        $c                                              => $None,    # "c"
        $AppT($x, $c)                                   => $None,    # (x "c")
        $AppT($x, $x)                                   => $None,    # (x x)
        $AppT($x, $y)                                   => $None,    # (x y)
        $LamT($x, $c)                                   => $None,    # (λx."c")
        $LamT($x, $x)                                   => $None,    # (λx.x)
        $LamT($x, $AppT($x, $x))                        => $None,    # (λx.x x)
        $LamT($x, $AppT($x, $c))                        => $None,    # (λx.x "c")
        $LamT($x, $AppT($x, $y))                        => $None,    # (λx.x y)

        $LamT($x, $AppT($y, $x))                        => $Some($y),                          # (λx.y x)      # a redex
        $LamT($x, $AppT($x, $LamT($y, $AppT($x, $y))))  => $Some($LamT($x, $AppT($x, $x))),    # (λx.x λy.x y)         # not a redex but reducible
        $AppT($LamT($y, $AppT($x, $y)), $y)             => $Some($AppT($x, $y)),               # ((λy.x y) y)          # not a redex but reducible

        $LamT($x, $AppT($LamT($y, $AppT($x, $y)), $x))  => $Some($LamT($x, $AppT($x, $x))),    # (λx.(λy.x y) x)       # not a redex but reducible
        $LamT($x, $AppT($LamT($x, $AppT($x, $y)), $x))  => $Some($LamT($x, $AppT($x, $y))),    # (λx.(λx.x y) x)       # a redex
    );


    my ($t, $ecd1, $ecd2, $expectedErd);

    # ((λx.y x) (λy.x y)) can contract twice; NO prescribed order!
    $t = $AppT($LamT($x, $AppT($y, $x)), $LamT($y, $AppT($x, $y)));  # not a redex but reducible (twice)
    subtest({
        $ecd1 = $etaContract($t);
        is($is-Some($ecd1), $true, "{$Term2source($t)} should eta-contract (at least) once") or die;
        $ecd1 = $Some2value($ecd1);
        # Note: we don't restrict the order in which parts are being contracted
        is($is-etaReducible($ecd1), $true, "(Some->value (etaContract {$Term2source($t)})) should still be eta-reducible") or die;
        $ecd2 = $etaContract($ecd1);
        is($is-Some($ecd2), $true, "{$Term2source($ecd1)} should eta-contract once more") or die;
        $ecd2 = $Some2value($ecd2);
        is($is-etaReducible($ecd2), $false,
            "(Some->value (etaContract {$Term2source($ecd1)})) should not be eta-reducible any further") or die;
        $expectedErd = $AppT($y, $x);   #  ((λx.y x) (λy.x y)) =_η (y x)
        is($ecd2, $expectedErd, 
            "(Some->value (etaContract {$Term2source($ecd1)})) should be {$Term2source($expectedErd)}") or die;
    }, "{$Term2source($t)} can contract twice; NO prescribed order!");

    # (λx.(λy.z y) x) can contract twice; prescribe order to outer-then-inner!
    $t = $LamT($x, $AppT($LamT($y, $AppT($z, $y)), $x));  # a redex (with inner redex)
    subtest({
        $ecd1 = $etaContract($t);
        is($is-Some($ecd1), $true, "{$Term2source($t)} should eta-contract (at least) once") or die;
        $ecd1 = $Some2value($ecd1);
        is($is-etaReducible($ecd1), $true, "(Some->value (etaContract {$Term2source($t)})) should still be eta-reducible") or die;
        
        # Note: we DO restrict the order here: from outer to inner:
        my $expectedEcd1 = $LamT($y, $AppT($z, $y));    # (λx.(λy.z y) x) |>_η (λy.z y)
        is($ecd1, $expectedEcd1, "{$Term2source($t)} should eta-contract in one step to {$Term2source($expectedEcd1)}") or die;
        
        $ecd2 = $etaContract($ecd1);
        is($is-Some($ecd2), $true, "{$Term2source($ecd1)} should eta-contract once more") or die;
        $ecd2 = $Some2value($ecd2);
        is($is-etaReducible($ecd2), $false,
            "(Some->value (etaContract {$Term2source($ecd1)})) should not be eta-reducible any further") or die;
        $expectedErd = $z;    # (λy.z y) |>_η z
        is($ecd2, $expectedErd, 
            "{$Term2source($ecd1)} should eta-contract to {$Term2source($expectedErd)}") or die;
    }, "{$Term2source($t)} can contract twice; prescribe order to outer-then-inner!");
}


{ # function etaReduce
    is_properLambdaFn($etaReduce);

    is $etaReduce.symbol, 'etaReduce', '$etaReduce.symbol';
    is $etaReduce.Str,    'etaReduce', '$etaReduce.Str';

    my sub etaReducesTo(*@tests) {
        for @tests -> $test {
            my $term       = $test.key;
            my $termStr    = $Term2source($term);
            my $expected   = $test.value;
            my $toItself = $expected === $None;
            my $expStr  = $toItself
                ?? "itself"
                !! '(Some ' ~ $Term2source($Some2value($expected)) ~ ')';
            my $desc = "$termStr eta-reduces to $expStr";

            subtest({
                my $actual = $etaReduce($term);
                is($actual, $expected, $desc)
                    or diag($actual.perl) and die;
                
                my $termP6 = convertToP6Term($term);

                my $expectedP6 = $toItself
                    ?? $termP6
                    !! convertToP6Term($Some2value($expected));

                is($termP6.eta-reduce, $expectedP6, $desc);
            }, $desc);
        }
    }

    my $x = $VarT('x');
    my $y = $VarT('y');
    my $z = $VarT('z');
    my $c = $ConstT('c');

    etaReducesTo(
        $x                                                          => $None,  # x
        $c                                                          => $None,  # "c"
        $AppT($x, $c)                                               => $None,  # (x "c")
        $AppT($x, $x)                                               => $None,  # (x x)
        $AppT($x, $y)                                               => $None,  # (x y)
        $LamT($x, $c)                                               => $None,  # (λx."c")
        $LamT($x, $x)                                               => $None,  # (λx.x)
        $LamT($x, $AppT($x, $x))                                    => $None,  # (λx.x x)
        $LamT($x, $AppT($x, $c))                                    => $None,  # (λx.x "c")
        $LamT($x, $AppT($x, $y))                                    => $None,  # (λx.x y)
        $LamT($x, $AppT($y, $x))                                    => $Some($y),                       # (λx.y x)              # a redex
        $LamT($x, $AppT($x, $LamT($y, $AppT($x, $y))))              => $Some($LamT($x, $AppT($x, $x))), # (λx.x λy.x y)         # not a redex but reducible
        $AppT($LamT($y, $AppT($x, $y)), $y)                         => $Some($AppT($x, $y)),            # ((λy.x y) y)          # not a redex but reducible
        $AppT($LamT($x, $AppT($y, $x)), $LamT($y, $AppT($x, $y)))   => $Some($AppT($y, $x)),            # ((λx.y x) (λy.x y))   # not a redex but reducible (contractible twice)
        $LamT($x, $AppT($LamT($y, $AppT($z, $y)), $x))              => $Some($z),                       # (λx.(λy.z y) x)       # a redex (with inner redex) (contractible twice)
        $LamT($x, $AppT($LamT($y, $AppT($x, $y)), $x))              => $Some($LamT($x, $AppT($x, $x))), # (λx.(λy.x y) x)       # not a redex but reducible
        $LamT($x, $AppT($LamT($x, $AppT($x, $y)), $x))              => $Some($LamT($x, $AppT($x, $y))), # (λx.(λx.x y) x)       # a redex
    );

}
