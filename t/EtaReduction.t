use v6;

use Test;
use Test::Util;

use Lambda::Boolean;
use Lambda::TermADT;
use Lambda::EtaReduction;

use Lambda::Conversion::Bool-conv;
use Lambda::LambdaGrammar;
use Lambda::LambdaModel;

plan 83;

sub test(Term:D $t, Str:D $desc, &tests) {
    #subtest {
     #   plan *;
        &tests($desc, $t)
    #}, $desc;
}


{ # predicate etaRedex?
    is_properLambdaFn($is-etaRedex);

    my sub is_etaRedex(*@tests) {
        for @tests -> $test {
            my $term       = $test.key;
            my $termStr    = $Term2Str($term).perl;
            my $expected   = $test.value;
            my $expectedP6 = convertTBool2P6Bool($expected);
            my $desc       = $expectedP6
                                ?? "$termStr is an eta redex" 
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
    my $t;

    is_etaRedex(
        $x                                                          => $false,  # x
        $c                                                          => $false,  # c
        $AppT($x, $c)                                               => $false,  # (x c)
        $AppT($x, $x)                                               => $false,  # (x x)
        $AppT($x, $y)                                               => $false,  # (x y)
        $LamT($x, $c)                                               => $false,  # (λx.c)
        $LamT($x, $x)                                               => $false,  # (λx.x)
        $LamT($x, $AppT($x, $x))                                    => $false,  # (λx.x x)
        $LamT($x, $AppT($x, $c))                                    => $false,  # (λx.x c)
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

{
    my $x = VarT.new(:name<x>);
    my $y = VarT.new(:name<y>);
    my $c = ConstT.new(:value('c'));
    my ($t, $desc);

    test $x, "a VarT", {
        is($^t.isEtaReducible,   False, "$^desc is not eta-reducible");
        cmp_ok($^t.eta-contract, '===', $^t, "$^desc eta-contracts to itself");
        my $erd = $^t.eta-reduce;
        cmp_ok($erd, '===', $^t, "$^desc eta-reduces to itself");
    };

    test $c, "a ConstT", {
        is($^t.isEtaReducible,   False, "$^desc is not eta-reducible");
        cmp_ok($^t.eta-contract, '===', $^t, "$^desc eta-contracts to itself");
        my $erd = $^t.eta-reduce;
        cmp_ok($erd, '===', $^t, "$^desc eta-reduces to itself");
    };


    { # (λx.c)
        test LamT.new(:var($x), :body($c)), "a LamT with body a ConstT", {
            is($^t.isEtaReducible,  False, "$^desc is not eta-reducible");
            cmp_ok($^t.eta-contract, '===', $^t, "$^desc eta-contracts to itself");
            my $erd = $^t.eta-reduce;
            cmp_ok($erd, '===', $^t, "$^desc eta-reduces to itself");
        };
    }

    test parseLambda('(λx.x)'), "a LamT with body a VarT", {
        is($^t.isEtaReducible,  False, "$^desc is not eta-reducible");
        cmp_ok($^t.eta-contract, '===', $^t, "$^desc eta-contracts to itself");
        my $erd = $^t.eta-reduce;
        cmp_ok($erd, '===', $^t, "$^desc eta-reduces to itself");
    };
    
    { # (λx.x c)
        test LamT.new(:var($x), :body(AppT.new(:func($x), :arg($c)))), 
            "a LamT with body an AppT where arg is a ConstT", {
            is($^t.isEtaReducible,  False, "$^desc is not eta-reducible");
            cmp_ok($^t.eta-contract, '===', $^t, "$^desc eta-contracts to itself");
            my $erd = $^t.eta-reduce;
            cmp_ok($erd, '===', $^t, "$^desc eta-reduces to itself");
        };
    }

    test parseLambda('(λx.x y)'), "a LamT with body an AppT where arg is a VarT other than the lambda's", {
        is($^t.isEtaReducible,  False, "$^desc is not eta-reducible");
        cmp_ok($^t.eta-contract, '===', $^t, "$^desc eta-contracts to itself");
        my $erd = $^t.eta-reduce;
        cmp_ok($erd, '===', $^t, "$^desc eta-reduces to itself");
    };

    test parseLambda('(λx.y x)'), "a LamT with body an AppT where arg is a VarT equal to the lambda's", {
        is($^t.isEtaReducible,  True,  "$^desc IS eta-reducible");
        my $ecd = $^t.eta-contract;
        cmp_ok($ecd, 'eq', parseLambda('y'), "$^desc eta-contracts to the AppT's func");
        my $erd = $^t.eta-reduce;
        cmp_ok($erd, '===', parseLambda('y'), "$^desc eta-reduces to the AppT's func");
    };

    test parseLambda('(λx.x x)'), "a LamT with body an AppT where arg is a VarT equal to the lambda's but free the AppT's func", {
        is($^t.isEtaReducible,  False,  "$^desc is NOT eta-reducible");
        my $ecd = $^t.eta-contract;
        cmp_ok($ecd, '===', $^t, "$^desc eta-contracts to itself");
        my $erd = $^t.eta-reduce;
        cmp_ok($erd, '===', $^t, "$^desc eta-reduces to itself");
    };

    test parseLambda('(λx.x λy.x y)'), "a LamT with body an AppT where arg is an eta-redex", {
        is($^t.isEtaReducible,  True,  "$^desc is itself eta-reducible");
        my $ecd = $^t.eta-contract;
        cmp_ok($ecd, 'eq', parseLambda('λx.x x'), "$^desc eta-contracts the AppT's arg");
        my $erd = $^t.eta-reduce;
        cmp_ok($erd, 'eq', parseLambda('λx.x x'), "$^desc eta-reduces to the AppT's arg");
    };

    { # (x c)
        test AppT.new(:func($x), :arg($c)), "an AppT (arg:ConstT)", {
            is($^t.isEtaReducible,   False, "$^desc is not eta-reducible");
            cmp_ok($^t.eta-contract, '===', $^t, "$^desc eta-contracts to itself");
            my $erd = $^t.eta-reduce;
            cmp_ok($erd, '===', $^t, "$^desc eta-reduces to itself");
        };
    }

    test parseLambda('(x y)'), "an AppT (func:VarT, arg:VarT)", {
        is($^t.isEtaReducible,   False, "$^desc is not eta-reducible");
        cmp_ok($^t.eta-contract, '===', $^t, "$^desc eta-contracts to itself");
        my $erd = $^t.eta-reduce;
        cmp_ok($erd, '===', $^t, "$^desc eta-reduces to itself");
    };

    test parseLambda('((λy.x y) y)'), "an AppT with an eta-redex as func", {
        is($^t.isEtaReducible,   True,  "$^desc IS eta-reducible");
        my $ecd = $^t.eta-contract;
        cmp_ok($ecd, 'eq', parseLambda('x y'), "$^desc eta-contracts the func");
        my $erd = $^t.eta-reduce;
        cmp_ok($erd, 'eq', parseLambda('x y'), "$^desc eta-reduces to the func's eta-reduction");
    };
    
    test parseLambda('y (λy.x y)'), "an AppT with an eta-redex as arg", {
        is($^t.isEtaReducible,   True,  "$^desc IS eta-reducible");
        my $ecd = $^t.eta-contract;
        cmp_ok($ecd, 'eq', parseLambda('y x'), "$^desc eta-contracts the arg");
        my $erd = $^t.eta-reduce;
        cmp_ok($erd, 'eq', parseLambda('y x'), "$^desc eta-reduces to the arg's eta-reduction");
    };
    
    test parseLambda('(λx.y x) (λy.x y)'), "an AppT with both, func and arg eta-redexes", {
        is($^t.isEtaReducible,   True,  "$^desc IS eta-reducible");
        my $ecd1 = $^t.eta-contract;
        is($ecd1.isEtaReducible,   True,  "$^desc eta-contracts to a still eta-reducible term");
        # Note: we don't restrict the order in which parts are being contracted
        my $ecd2 = $ecd1.eta-contract;
        cmp_ok($ecd2, 'eq', parseLambda('y x'), "$^desc eta-contracts in two steps the func and the arg");
        my $erd = $^t.eta-reduce;
        cmp_ok($erd, 'eq', parseLambda('y x'), "$^desc eta-reduces to the func's and arg's eta-reduction, resp.");
    };
    
    test parseLambda('(λx.(λy.z y) x) '), "a LamT with body an AppT where arg is the lambda's var and func an eta-redex", {
        is($^t.isEtaReducible,   True,  "$^desc is eta-reducible");
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
