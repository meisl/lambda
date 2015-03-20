use v6;
use Test;

use Lambda::BaseP6;
use Lambda::Boolean;
use Lambda::TermADT;
use Lambda::LambdaGrammar;


# modules under test:
use Test::Util;
use Test::Util_Lambda;
use Test::Util_Term;

plan 10;


{ # does_ok, is_properLambdaFn
    # using ::= to make it immutable
    my $bad   ::= ( { 23 } but lambda('not.a.valid)lambda(term') ) but Definition<bad> ;
    my $good1 ::= ( { 42 } but lambda('λx.x')                    ) but Definition<good1>;
    my $good2 ::=   { 11 } but lambda(('λx.x', 'good2'));

    is_properLambdaFn($good1, :noWarning);
    is_properLambdaFn($good1, 'good1');
    is_properLambdaFn($good2, :noWarning);
    is_properLambdaFn($good2, 'good2');

    # TODO: how to test this: `is_properLambdaFn($bad)`- should fail with X::Lambda::SyntaxError;
}

todo 'does_ok';
todo 'doesnt_ok';

todo '$contains_ok';
todo '$has_length';

{ # is_eq test for TTerms
    does_ok &is_eq, Callable, 'exports `&is_eq`';
    lives_ok({ is_eq($VarT('x'), $VarT('x')) }, 'can call &is_eq without msg string');
    lives_ok({ is_eq($VarT('x'), $VarT('x'), 'var x equals var x') }, 'can call &is_eq with a msg string');
}

subtest({ # prefix operator ` (for retrieving pre-built test-terms)
    my $x = $VarT('x');
    my $omegaX = $LamT('x', $AppT($x, $x));
    
    is_eq(`'x', $x, 'simple var x from %terms');
    
    is_eq(`'(λx.(x x))', $omegaX, 'omega as fully parenthesized lambda expr');
    is_eq(`'λx.(x x)',   $omegaX, 'omega as lambda expr without surrounding parens');
    is_eq(`'ωX',         $omegaX, 'omega as symbol ωX');
}, 'prefix op ` retrieves...');


#`{ # test the test-terms
    does_ok &testTermFn, Callable, 'exports `&testTermFn`';

    subtest({
        for %terms.pairs -> (:$key, :$value) {
            subtest({
                does_ok $value, TTerm;
                my TTerm $term = parseLambda($key);
                is_eq($term, $value);
            });
        }
    }, '%terms.keys are Str s and .values are TTerm s');
}

