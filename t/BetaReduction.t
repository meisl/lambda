use v6;

use Test;
use Lambda::LambdaGrammar;
use Lambda::LambdaModel;

plan 60;

sub test(Term:D $t, Str:D $desc, &tests) {
    #subtest {
     #   plan *;
        &tests("$t: $desc", $t)
    #}, $desc;
}

{
    my $x = λ('x');
    my $y = λ('y');
    my $c = ConstT.new(:value('c'));
    my ($t, $desc);

    test $x, "a VarT", {
        is($^t.isBetaRedex,       False, "$^desc is not a beta redex");
        is($^t.isBetaReducible,   False, "$^desc is not beta-reducible");
        cmp_ok($^t.beta-contract, '===', $^t, "$^desc beta-contracts to itself");
        my $erd = $^t.beta-reduce;
        cmp_ok($erd, '===', $^t, "$^desc beta-reduces to itself");
    };

    test $c, "a ConstT", {
        is($^t.isBetaRedex,       False, "$^desc is not a beta redex");
        is($^t.isBetaReducible,   False, "$^desc is not beta-reducible");
        cmp_ok($^t.beta-contract, '===', $^t, "$^desc beta-contracts to itself");
        my $erd = $^t.beta-reduce;
        cmp_ok($erd, '===', $^t, "$^desc beta-reduces to itself");
    };


    # (λx.c)
    test LamT.new(:var($x), :body($c)), "a LamT with body a ConstT", {
        is($^t.isBetaRedex,      False, "$^desc is not a beta redex");
        is($^t.isBetaReducible,  False, "$^desc is not beta-reducible");
        cmp_ok($^t.beta-contract, '===', $^t, "$^desc beta-contracts to itself");
        my $erd = $^t.beta-reduce;
        cmp_ok($erd, '===', $^t, "$^desc beta-reduces to itself");
    };

    test λ('(λx.x)'), "a LamT with body a VarT", {
        is($^t.isBetaRedex,      False, "$^desc is not a beta redex");
        is($^t.isBetaReducible,  False, "$^desc is not beta-reducible");
        cmp_ok($^t.beta-contract, '===', $^t, "$^desc beta-contracts to itself");
        my $erd = $^t.beta-reduce;
        cmp_ok($erd, '===', $^t, "$^desc beta-reduces to itself");
    };
    
    # (λx.x c)
    test LamT.new(:var($x), :body(AppT.new(:func($x), :arg($c)))), 
        "a LamT with body an AppT where arg is a ConstT", {
        is($^t.isBetaRedex,      False, "$^desc is not a beta redex");
        is($^t.isBetaReducible,  False, "$^desc is not beta-reducible");
        cmp_ok($^t.beta-contract, '===', $^t, "$^desc beta-contracts to itself");
        my $erd = $^t.beta-reduce;
        cmp_ok($erd, '===', $^t, "$^desc beta-reduces to itself");
    };

    test λ('(λx.x y)'), "a LamT with body an AppT where arg is a VarT other than the lambda's", {
        is($^t.isBetaRedex,      False, "$^desc is not a beta redex");
        is($^t.isBetaReducible,  False, "$^desc is not beta-reducible");
        cmp_ok($^t.beta-contract, '===', $^t, "$^desc beta-contracts to itself");
        my $erd = $^t.beta-reduce;
        cmp_ok($erd, '===', $^t, "$^desc beta-reduces to itself");
    };

    test λ('(λx.y x)'), "a LamT with body an AppT where arg is a VarT equal to the lambda's", {
        is($^t.isBetaRedex,      False, "$^desc is not a beta redex");
        is($^t.isBetaReducible,  False, "$^desc is not beta-reducible");
        my $ecd = $^t.beta-contract;
        cmp_ok($ecd, '===', $^t, "$^desc beta-contracts to itself");
    };

    test λ('(λx.x x)'), "a LamT with body an AppT where arg is a VarT equal to the lambda's but free the AppT's func", {
        is($^t.isBetaRedex,      False,  "$^desc is NOT a beta redex");
        is($^t.isBetaReducible,  False,  "$^desc is NOT beta-reducible");
        my $ecd = $^t.beta-contract;
        cmp_ok($ecd, '===', $^t, "$^desc beta-contracts to itself");
        my $erd = $^t.beta-reduce;
        cmp_ok($erd, '===', $^t, "$^desc beta-reduces to itself");
    };

    test λ('(λx.x ((λy.λz.y x) (λy.x y)))'), "a LamT with body an AppT where func is a VarT and arg is a beta-redex", {
        is($^t.isBetaRedex,      False, "$^desc is not itself a beta redex");
        is($^t.isBetaReducible,  True,  "$^desc is itself beta-reducible");
        my $ecd = $^t.beta-contract;
        cmp_ok($ecd, 'eq', λ('λx.x (λz.(λy.x y) x)'), "$^desc beta-contracts the AppT's arg");
        my $erd = $^t.beta-reduce;
        cmp_ok($erd, 'eq', λ('λx.x λz.x x'), "$^desc beta-reduces in two steps");
    };


    # (x c)
    test AppT.new(:func($x), :arg($c)), "an AppT (arg:ConstT)", {
        is($^t.isBetaRedex,       False, "$^desc is not a beta redex");
        is($^t.isBetaReducible,   False, "$^desc is not beta-reducible");
        cmp_ok($^t.beta-contract, '===', $^t, "$^desc beta-contracts to itself");
        my $erd = $^t.beta-reduce;
        cmp_ok($erd, '===', $^t, "$^desc beta-reduces to itself");
    };

    # 40...
    test λ('(x y)'), "an AppT (func:VarT, arg:VarT)", {
        is($^t.isBetaRedex,       False, "$^desc is not a beta redex");
        is($^t.isBetaReducible,   False, "$^desc is not beta-reducible");
        cmp_ok($^t.beta-contract, '===', $^t, "$^desc beta-contracts to itself");
        my $erd = $^t.beta-reduce;
        cmp_ok($erd, '===', $^t, "$^desc beta-reduces to itself");
    };

    # 44...
    test λ('((λy.x y) y) z'), "an AppT with a beta-redex as func", {
        is($^t.isBetaRedex,       False, "$^desc is not itself a beta redex");
        is($^t.isBetaReducible,   True,  "$^desc IS beta-reducible");
        my $ecd = $^t.beta-contract;
        cmp_ok($ecd, 'eq', λ('(x y) z'), "$^desc beta-contracts the func");
        my $erd = $^t.beta-reduce;
        cmp_ok($erd, 'eq', λ('(x y) z'), "$^desc beta-reduces to the func's beta-reduction");
    };
    
    # 48...
    test λ('y ((λy.x y) z)'), "an AppT with a beta-redex as arg", {
        is($^t.isBetaRedex,       False, "$^desc is not necessarily itself a beta redex");
        is($^t.isBetaReducible,   True,  "$^desc IS beta-reducible");
        my $ecd = $^t.beta-contract;
        cmp_ok($ecd, 'eq', λ('y (x z)'), "$^desc beta-contracts the arg");
        my $erd = $^t.beta-reduce;
        cmp_ok($erd, 'eq', λ('y (x z)'), "$^desc beta-reduces to the arg's beta-reduction");
    };
    
    # 52...
    test λ('((λx.y) x) ((λy.x) y)'), "an AppT with both, func and arg beta-redexes", {
        is($^t.isBetaRedex,       False, "$^desc is not itself a beta redex");
        is($^t.isBetaReducible,   True,  "$^desc IS beta-reducible");
        my $ecd1 = $^t.beta-contract;
        is($ecd1.isBetaReducible,   True,  "$^desc beta-contracts to a still beta-reducible term");
        # Note: we don't restrict the order in which parts are being contracted
        my $ecd2 = $ecd1.beta-contract;
        cmp_ok($ecd2, 'eq', λ('y x'), "$^desc beta-contracts in two steps the func and the arg");
        my $erd = $^t.beta-reduce;
        cmp_ok($erd, 'eq', λ('y x'), "$^desc beta-reduces to the func's and arg's beta-reduction, resp.");
    };
    
    # 57...
    test λ('(λx.((λy.z y) x) x) '), "a LamT with body an AppT where func is a beta-redex and arg a VarT", {
        is($^t.isBetaRedex,       False, "$^desc is not itself a beta redex");
        is($^t.isBetaReducible,   True,  "$^desc IS beta-reducible");
        my $bcd = $^t.beta-contract;
        is($bcd.isBetaReducible,  False, "$^desc beta-contracts to a non-beta-reducible term");

        cmp_ok($bcd, 'eq', λ('λx.(z x) x'), "$^desc beta-contracts the inner lambda");
        # TODO: use as example for beta-eta reduction
    };

}

# examples requiring alpha-conversion before substitution:
todo {

    test λ('(λx.x ((λy.λz.y x) (x y z)))'), "a LamT with body an AppT where arg is a beta-redex", {
        is($^t.isBetaRedex,      False, "$^desc is not itself a beta redex");
        is($^t.isBetaReducible,  True,  "$^desc is itself beta-reducible");
        my $ecd = $^t.beta-contract;
        cmp_ok($ecd, 'eq', λ('λx.x x'), "$^desc beta-contracts the AppT's arg");
        my $erd = $^t.beta-reduce;
        cmp_ok($erd, 'eq', λ('λx.x x'), "$^desc beta-reduces to the AppT's arg");
    };

}
