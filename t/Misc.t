use v6;
use Test;
use Test::Util;
use Test::Util_Lambda;

use Lambda::MaybeADT;
use Lambda::Boolean;
use Lambda::TermADT;
use Lambda::FreeVars;
use Lambda::EtaReduction;
use Lambda::BetaReduction;

use Lambda::LambdaGrammar;
use Lambda::Conversion;


# module(s) under test:
use Lambda::String;

plan 3;


subtest({ # Str-concat
    is_properLambdaFn($Str-concat, 'Str-concat');

    is $Str-concat("a", "a"), "aa";
    is $Str-concat("a", "b"), "ab";
    is $Str-concat("b", "a"), "ba";

    is $Str-concat("", "a"), "a";
    is $Str-concat("a", ""), "a";

    is $Str-concat("foo", "bar"), "foobar";
}, 'Str-concat');

subtest({ # Str-eq?
    is_properLambdaFn($Str-eq, 'Str-eq?');

    is $Str-eq("a", "a"), $true;
    is $Str-eq("the λ calculus", "the λ calculus"), $true;
    is $Str-eq("The λ calculus", "the λ calculus"), $false;

    is $Str-eq("a", "b"), $false;
    is $Str-eq("b", "a"), $false;
    is $Str-eq("a", ""), $false;
    is $Str-eq("", "b"), $false;
    is $Str-eq("", ""), $true;

    dies_ok({ $Str-eq(Str, 'x') }, 'cannot call it with 1st arg undefined');
    dies_ok({ $Str-eq('x', Str) }, 'cannot call it with 2nd arg undefined');
    dies_ok({ $Str-eq(Str, Str) }, 'cannot call it with both args undefined');

    dies_ok({ $Str-eq(456, 'x') }, 'cannot call it with 1st arg an Int');
    dies_ok({ $Str-eq('x', 456) }, 'cannot call it with 2nd arg an Int');
    dies_ok({ $Str-eq(123, 456) }, 'cannot call it with both args Ints');

    my $partial = $Str-eq('foo');
    is $partial('foo'), $true, 'partial application (1)';
    is $partial('bar'), $false, 'partial application (2)';
}, 'Str-eq?');


subtest({ # Str-ne?
    is_properLambdaFn($Str-ne, 'Str-ne?');

    is $Str-ne("a", "a"), $false;
    is $Str-ne("the λ calculus", "the λ calculus"), $false;
    is $Str-ne("The λ calculus", "the λ calculus"), $true;

    is $Str-ne("a", "b"), $true;
    is $Str-ne("b", "a"), $true;
    is $Str-ne("a", ""), $true;
    is $Str-ne("", "b"), $true;
    is $Str-ne("", ""), $false;

    dies_ok({ $Str-ne(Str, 'x') }, 'cannot call it with 1st arg undefined');
    dies_ok({ $Str-ne('x', Str) }, 'cannot call it with 2nd arg undefined');
    dies_ok({ $Str-ne(Str, Str) }, 'cannot call it with both args undefined');

    dies_ok({ $Str-ne(456, 'x') }, 'cannot call it with 1st arg an Int');
    dies_ok({ $Str-ne('x', 456) }, 'cannot call it with 2nd arg an Int');
    dies_ok({ $Str-ne(123, 456) }, 'cannot call it with both args Ints');

    my $partial = $Str-ne('foo');
    is $partial('foo'), $false, 'partial application (1)';
    is $partial('bar'), $true, 'partial application (2)';
}, 'Str-ne?');


# ------------------------------------------------------------------------------------------------

{
    my ($n, $apvs, $apvsP6);

    $n = parseLambda('(λx.λz.λv.z x (λx.x) (λz.x z) (λy.x x)) ((z ((λx.λy.x y z) x)) v)');
    my TTerm $func    = $AppT2func($n);
    my TTerm $arg     = $AppT2arg($n);
    my Str   $varName = $LamT2var($func);    # DONE: LamT_ctor_with_Str_binder
    my TTerm $var     = $VarT($varName);
    my TTerm $body    = $LamT2body($func);
    say $Term2source($n);
    say 'β-redex? '~ $is-betaRedex($n);
    say 'β-reducible? '~ $is-betaReducible($n);
    say 'FV: '~ $free-vars($n);
    $apvs   = $alpha-problematic-vars($n);
    $apvsP6 = convertTList2P6Array($apvs);
    say '(alpha-problematic-vars ...) = ' ~ $apvsP6.map($Term2source).join(", ");
    my ($ants, $antsP6);
    $ants = $alpha-needy-terms($n, $apvs);
    say "n.α-needy-terms:\n  " ~ convertTList2P6Array($ants).map($Term2source).join("\n  ");
    $ants = $alpha-needy-terms($func, $apvs);
    say "func.α-needy-terms:\n  " ~ convertTList2P6Array($ants).map($Term2source).join("\n  ");

    say '';
    say $Term2source($func);
    say 'β-redex? '~ $is-betaRedex($func);
    say 'β-reducible? '~ $is-betaReducible($func);
    say 'FV: '~ $free-vars($func);
    say '(freeName-under? x z ...) ' ~ $is-freeName-under($varName, 'z', $body);
    say '(freeName-under? x x ...) ' ~ $is-freeName-under($varName, 'x', $body);
    say '(freeName-under? x v ...) ' ~ $is-freeName-under($varName, 'v', $body);

    say '';
    say $Term2source($arg);
    say 'β-redex? '~ $is-betaRedex($arg);
    say 'β-reducible? '~ $is-betaReducible($arg);
    say 'FV: '~ $free-vars($arg);
}

{
    my $n;

    $n = parseLambda('λf.(λx.λy.(f g h x y))');
    say $Term2source($n);
    my $n_smp = $Some2value($etaContract($n));
    say "eta-contract (only):\n{$Term2source($n_smp)}";
    say 'η-reducible? ' ~ $is-etaReducible($n_smp);
    say $Term2source($Some2value($etaContract($n_smp)));
    say $Term2source($Some2value($etaReduce($n)));

#    my $n_evd = $n.eval-s;
#    say "eval-s:\n$n_evd\n";
#    say $n_evd;
    
#    my $n_evd_smp = $n_evd.simplify;
#    say "eval-s + simplify:\n$n_evd_smp\n";
#    say $n_evd_smp;
}

{
    my %texts = %(              # chi: χ0
        1 => '(λx.(x (λa.(λb.a))))',
        2 => 'λx.x λa.λb.a',
        7 => 'λx.x',
        3 => '(f _)',
        8 => '(δ id λx.x)',

        # Church numerals
        9 => '(δ χ0 λf.λx.x)  (δ χ1 λf.λx.f x)  (δ χ2 λf.λx.f (f x))  (δ χ3 λf.λx.f (f (f x)))'
            #'(δ χ0 λf.id)    (δ χ1 id)'
             ~'  (δ succ λn.λf.λx.n f (f x))',
             #'  (δ succ λn.λf.λx.f (n f x))',
        4 => '(δ id λx.x)  (δ fst λa.λb.a)  (δ snd λa.λb.b)  (δ reverse-apply λa.λf.f a)  (δ car (reverse-apply fst))',
        5 => '(δ id λx.x)  (δ fst λa.λb.a)  (δ snd λa.λb.b)',
        6 => '(δ let λvar.λterm.λbody.(λvar.body) term)',
        10 => '(λa.λb.a) (λf.λx.x) (λf.f)',
    );
}

{
    #$succ-of-zero_a:
    #a: (λf.(λx.(((λg.(λx.x)) f) (f x))))
    #   (λf.(λx.(     (λx.x)     (f x))))   # App.simplify-ident
    #   (λf.(λx.                 (f x)))    # Abs.simplify-curry
    #   (λf.                      f)
 
    #b: (λf.(λx.(f (((λg.(λx.x)) f) x))))
    #   (λf.(λx.(f (     (λx.x)     x))))   # App.simplify-ident
    #   (λf.(λx.(f                  x)))    # Abs.simplify-curry
    #   (λf.     f)
}

{
    my $succ-of-zero_a = '(λn.λf.λx.n f (f x)) (λf.λx.x)';
    my $succ-of-zero_b = '(λn.λf.λx.f (n f x)) (λf.λx.x)';

    my $test-simplify_curry = 'λf.λx.f x';
    my $test-simplify_ident = '(λx.x) (λx.x)';
    my $test-simplify_ident_a = '(λf.(λx.((λx.x) (f x))))';
    my $test-simplify_ident_b = '(λf.(λx.(f ((λx.x) x))))';
}
