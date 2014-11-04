use v6;

use Test;
use Test::Util;

use Lambda::Boolean;
use Lambda::MaybeADT;
use Lambda::TermADT;
use Lambda::EtaReduction;

use Lambda::Conversion::Bool-conv;
use Lambda::LambdaGrammar;
use Lambda::LambdaModel;

plan 140;

sub test(Term:D $t, Str:D $desc, &tests) {
    #subtest {
     #   plan *;
        &tests($desc, $t)
    #}, $desc;
}


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
            
            cmp_ok($is-etaRedex($term), '===', $expected, $desc);
            
            my $termP6 = convertToP6Term($term);
            cmp_ok($termP6.isEtaRedex, '===', $expectedP6, $desc);
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
            
            cmp_ok($is-etaReducible($term), '===', $expected, $desc);
            
            my $termP6 = convertToP6Term($term);
            cmp_ok($termP6.isEtaReducible, '===', $expectedP6, $desc);
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

    my sub etaContractsTo(TTerm:D $term, $expected) {
        my $termStr = $Term2source($term);
        my $toItself = $expected === $None;
        my $expStr  = $toItself
            ?? "itself"
            !! '(Some ' ~ $Term2source($Some2value($expected)) ~ ')';
        my $desc = "$termStr eta-contracts to $expStr";

        is($etaContract($term), $expected, $desc)
            or die;
        
        my $termP6 = convertToP6Term($term);

        my $expectedP6 = $toItself
            ?? $termP6
            !! convertToP6Term($Some2value($expected));

        is($termP6.eta-contract, $expectedP6, $desc);
    }

    my $x = $VarT('x');
    my $y = $VarT('y');
    my $z = $VarT('z');
    my $c = $ConstT('c');

    etaContractsTo($x,                                                         $None);    # x
    etaContractsTo($c,                                                         $None);    # "c"
    etaContractsTo($AppT($x, $c),                                              $None);    # (x "c")
    etaContractsTo($AppT($x, $x),                                              $None);    # (x x)
    etaContractsTo($AppT($x, $y),                                              $None);    # (x y)
    etaContractsTo($LamT($x, $c),                                              $None);    # (λx."c")
    etaContractsTo($LamT($x, $x),                                              $None);    # (λx.x)
    etaContractsTo($LamT($x, $AppT($x, $x)),                                   $None);    # (λx.x x)
    etaContractsTo($LamT($x, $AppT($x, $c)),                                   $None);    # (λx.x "c")
    etaContractsTo($LamT($x, $AppT($x, $y)),                                   $None);    # (λx.x y)

    etaContractsTo($LamT($x, $AppT($y, $x)),                                   $Some($y)                       );    # (λx.y x)      # a redex
    etaContractsTo($LamT($x, $AppT($x, $LamT($y, $AppT($x, $y)))),             $Some($LamT($x, $AppT($x, $x))) );   # (λx.x λy.x y)         # not a redex but reducible
    etaContractsTo($AppT($LamT($y, $AppT($x, $y)), $y),                        $Some($AppT($x, $y))            );   # ((λy.x y) y)          # not a redex but reducible
    
    # can contract twice; DON'T prescribe the order!
    #etaContractsTo($AppT($LamT($x, $AppT($y, $x)), $LamT($y, $AppT($x, $y))),   );   # ((λx.y x) (λy.x y))   # not a redex but reducible (twice)

    # can contract twice; DON'T prescribe the order!
    #etaContractsTo($LamT($x, $AppT($LamT($y, $AppT($z, $y)), $x)),              );   # (λx.(λy.z y) x)       # a redex (with inner redex)

    etaContractsTo($LamT($x, $AppT($LamT($y, $AppT($x, $y)), $x)),             $Some($LamT($x, $AppT($x, $x))) );   # (λx.(λy.x y) x)       # not a redex but reducible
    etaContractsTo($LamT($x, $AppT($LamT($x, $AppT($x, $y)), $x)),             $Some($LamT($x, $AppT($x, $y))) );   # (λx.(λx.x y) x)       # a redex
}

{
    my $x = VarT.new(:name<x>);
    my $y = VarT.new(:name<y>);
    my $c = ConstT.new(:value('c'));
    my ($t, $desc);

    test $x, "a VarT", {
        cmp_ok($^t.eta-contract, '===', $^t, "$^desc eta-contracts to itself");
        my $erd = $^t.eta-reduce;
        cmp_ok($erd, '===', $^t, "$^desc eta-reduces to itself");
    };

    test $c, "a ConstT", {
        cmp_ok($^t.eta-contract, '===', $^t, "$^desc eta-contracts to itself");
        my $erd = $^t.eta-reduce;
        cmp_ok($erd, '===', $^t, "$^desc eta-reduces to itself");
    };


    { # (λx.c)
        test LamT.new(:var($x), :body($c)), "a LamT with body a ConstT", {
            cmp_ok($^t.eta-contract, '===', $^t, "$^desc eta-contracts to itself");
            my $erd = $^t.eta-reduce;
            cmp_ok($erd, '===', $^t, "$^desc eta-reduces to itself");
        };
    }

    test parseLambda('(λx.x)'), "a LamT with body a VarT", {
        cmp_ok($^t.eta-contract, '===', $^t, "$^desc eta-contracts to itself");
        my $erd = $^t.eta-reduce;
        cmp_ok($erd, '===', $^t, "$^desc eta-reduces to itself");
    };
    
    { # (λx.x c)
        test LamT.new(:var($x), :body(AppT.new(:func($x), :arg($c)))), 
            "a LamT with body an AppT where arg is a ConstT", {
            cmp_ok($^t.eta-contract, '===', $^t, "$^desc eta-contracts to itself");
            my $erd = $^t.eta-reduce;
            cmp_ok($erd, '===', $^t, "$^desc eta-reduces to itself");
        };
    }

    test parseLambda('(λx.x y)'), "a LamT with body an AppT where arg is a VarT other than the lambda's", {
        cmp_ok($^t.eta-contract, '===', $^t, "$^desc eta-contracts to itself");
        my $erd = $^t.eta-reduce;
        cmp_ok($erd, '===', $^t, "$^desc eta-reduces to itself");
    };

    test parseLambda('(λx.y x)'), "a LamT with body an AppT where arg is a VarT equal to the lambda's", {
        my $ecd = $^t.eta-contract;
        cmp_ok($ecd, 'eq', parseLambda('y'), "$^desc eta-contracts to the AppT's func");
        my $erd = $^t.eta-reduce;
        cmp_ok($erd, '===', parseLambda('y'), "$^desc eta-reduces to the AppT's func");
    };

    test parseLambda('(λx.x x)'), "a LamT with body an AppT where arg is a VarT equal to the lambda's but free the AppT's func", {
        my $ecd = $^t.eta-contract;
        cmp_ok($ecd, '===', $^t, "$^desc eta-contracts to itself");
        my $erd = $^t.eta-reduce;
        cmp_ok($erd, '===', $^t, "$^desc eta-reduces to itself");
    };

    test parseLambda('(λx.x λy.x y)'), "a LamT with body an AppT where arg is an eta-redex", {
        my $ecd = $^t.eta-contract;
        cmp_ok($ecd, 'eq', parseLambda('λx.x x'), "$^desc eta-contracts the AppT's arg");
        my $erd = $^t.eta-reduce;
        cmp_ok($erd, 'eq', parseLambda('λx.x x'), "$^desc eta-reduces to the AppT's arg");
    };

    { # (x c)
        test AppT.new(:func($x), :arg($c)), "an AppT (arg:ConstT)", {
            cmp_ok($^t.eta-contract, '===', $^t, "$^desc eta-contracts to itself");
            my $erd = $^t.eta-reduce;
            cmp_ok($erd, '===', $^t, "$^desc eta-reduces to itself");
        };
    }

    test parseLambda('(x y)'), "an AppT (func:VarT, arg:VarT)", {
        cmp_ok($^t.eta-contract, '===', $^t, "$^desc eta-contracts to itself");
        my $erd = $^t.eta-reduce;
        cmp_ok($erd, '===', $^t, "$^desc eta-reduces to itself");
    };

    test parseLambda('((λy.x y) y)'), "an AppT with an eta-redex as func", {
        my $ecd = $^t.eta-contract;
        cmp_ok($ecd, 'eq', parseLambda('x y'), "$^desc eta-contracts the func");
        my $erd = $^t.eta-reduce;
        cmp_ok($erd, 'eq', parseLambda('x y'), "$^desc eta-reduces to the func's eta-reduction");
    };
    
    test parseLambda('y (λy.x y)'), "an AppT with an eta-redex as arg", {
        my $ecd = $^t.eta-contract;
        cmp_ok($ecd, 'eq', parseLambda('y x'), "$^desc eta-contracts the arg");
        my $erd = $^t.eta-reduce;
        cmp_ok($erd, 'eq', parseLambda('y x'), "$^desc eta-reduces to the arg's eta-reduction");
    };
    
    test parseLambda('(λx.y x) (λy.x y)'), "an AppT with both, func and arg eta-redexes", {
        my $ecd1 = $^t.eta-contract;
        is($ecd1.isEtaReducible,   True,  "$^desc eta-contracts to a still eta-reducible term");
        # Note: we don't restrict the order in which parts are being contracted
        my $ecd2 = $ecd1.eta-contract;
        cmp_ok($ecd2, 'eq', parseLambda('y x'), "$^desc eta-contracts in two steps the func and the arg");
        my $erd = $^t.eta-reduce;
        cmp_ok($erd, 'eq', parseLambda('y x'), "$^desc eta-reduces to the func's and arg's eta-reduction, resp.");
    };
    
    test parseLambda('(λx.(λy.z y) x) '), "a LamT with body an AppT where arg is the lambda's var and func an eta-redex", {
        my $ecd1 = $^t.eta-contract;
        is($ecd1.isEtaReducible,   True,  "$^desc eta-contracts to a still eta-reducible term");
        # Note: here we do restrict the order to outer-to-inner
        cmp_ok($ecd1, 'eq', parseLambda('λy.z y'), "$^desc eta-contracts to the inner lambda");
        my $ecd2 = $ecd1.eta-contract;
        cmp_ok($ecd2, 'eq', parseLambda('z'), "$^desc eta-contracts in two steps to the inner lambda's func");
        my $erd = $^t.eta-reduce;
        cmp_ok($erd, 'eq', parseLambda('z'), "$^desc eta-reduces to the inner lambda's func");
    };

}
