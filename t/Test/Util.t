use v6;
use Test;

use Lambda::BaseP6;
use Lambda::Boolean;
use Lambda::ListADT;
use Lambda::TermADT;
use Lambda::LambdaGrammar;


# modules under test:
use Test::Util;
use Test::Util_Lambda;
use Test::Util_List;
use Test::Util_Term;

plan 17;


# - Util_List -----------------------------------------------------------------

{
    is_eq-List($nil, [], "nil equals []");
    is_eq-List($cons(5, $nil), [5]);
    is_eq-List($cons(5, $cons(3, $nil)), [5, 3]);
    
    ## elems differ:
    #is_eq-List($cons(5, $nil),                       [3]);       # TODO: should fail (dunno how to test this)
    
    ## actual has too few elems:
    #is_eq-List($cons(5, $cons(3, $nil)),             [5, 4]);    # TODO: should fail (dunno how to test this)
    #is_eq-List($cons(5, $nil),                       [5, 3, 1]); # TODO: should fail (dunno how to test this)
    #is_eq-List($cons(5, $nil),                       [5, 3]);    # TODO: should fail (dunno how to test this)
    
    ## actual has too many elems:
    #is_eq-List($cons(5, $cons(3, $nil)),             [5]);       # TODO: should fail (dunno how to test this)
    #is_eq-List($cons(5, $cons(3, $cons(1, $nil))),   [5]);       # TODO: should fail (dunno how to test this)

    subtest({
        my $list;

        $list = $nil;
        $has_length($list, 0, $list.Str);

        $list = $cons(5, $nil);
        $has_length($list, 1, $list.Str);

        $list = $cons(5, $cons(3, $nil));
        $has_length($list, 2, $list.Str);

        $list = $cons(5, $cons("foo", $cons(3, $nil)));
        $has_length($list, 3, $list.Str);

        # now lists containing other lists somewhere inside:
        my $list_3 = $cons(3, $nil);
        my $list_foo_3 = $cons("foo", $list_3);
        $list = $cons(5, $cons($list_foo_3, $nil));
        $has_length($list, 2, $list.Str);

        my $list_bar_3 = $cons("bar", $list_3);
        my $list_foo   = $cons("foo", $nil);
        my $list_list_bar_3 = $cons($list_bar_3, $nil);
        $list = $cons(5, $cons($list_foo, $cons($list_list_bar_3, $nil)));
        $has_length($list, 3, $list.Str);

    }, '$has_length');

    todo '$contains_ok';
}


# - Util ----------------------------------------------------------------------
{
    todo 'does_ok';
    todo 'doesnt_ok';
}


# - Util_Lambda ---------------------------------------------------------------

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


# - Util_Term -----------------------------------------------------------------

{ # is_eq test for TTerms
    does_ok &is_eq-Term, Callable, 'exports `&is_eq-Term`';
    lives_ok({ is_eq-Term($VarT('x'), $VarT('x')) }, 'can call &is_eq-Term without msg string');
    lives_ok({ is_eq-Term($VarT('x'), $VarT('x'), 'var x equals var x') }, 'can call &is_eq-Term with a msg string');
}

subtest({ # prefix operator ` (for retrieving pre-built test-terms)
    my $x = $VarT('x');
    my $omegaX = $LamT('x', $AppT($x, $x));
    
    is_eq-Term(`'x', $x, 'simple var x from %terms');
    
    is_eq-Term(`'(λx.(x x))', $omegaX, 'omega as fully parenthesized lambda expr');
    is_eq-Term(`'λx.(x x)',   $omegaX, 'omega as lambda expr without surrounding parens');
    is_eq-Term(`'ωX',         $omegaX, 'omega as symbol ωX');
}, 'prefix op ` retrieves...');


{ # test the test-terms
    does_ok &testTermFn, Callable, 'exports `&testTermFn`';
    does_ok $testTerms, Any, 'exports `$testTerms`';

    subtest({
        for $testTerms.values -> $value {
            subtest({
                my $mainKey = $value.mainKey;
                is $mainKey, $Term2srcFull($value), "main key {$mainKey.perl} should be fully parenthesized lambda expr";

                my TTerm $term = parseLambda($mainKey);
                is_eq-Term($term, $value);

                for $value.synonyms -> $s {
                    my $sValue = $testTerms.get($s);
                    cmp_ok($sValue, '===', $value, "value for synonym {$s.perl}")
                        or die;
                    lives_ok({ parseLambda($s) }, "synonym {$s.perl} is a valid lambda expr")
                        or die;
                }
            }) unless $value.Str eq '(ConstT 5)';   # TODO: add (decimal) number constant literals to grammar
        }
    }, 'test-terms');
}

