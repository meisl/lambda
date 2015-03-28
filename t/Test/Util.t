use v6;
use Test;

use Lambda::BaseP6;
use Lambda::Boolean;
use Lambda::String;
use Lambda::PairADT;
use Lambda::ListADT;
use Lambda::TermADT;
use Lambda::LambdaGrammar;


# modules under test:
use Test::Util;
use Test::Util_Lambda;
use Test::Util_List;
use Test::Util_Term;

plan 21;


# - Util_Term -----------------------------------------------------------------

subtest({ # testTermFn
    does_ok &testTermFn, Callable, 'is exported';

    my @receivedArgs;
    my sub makeF(*@expectedResults) {
        return -> |args {
            @receivedArgs.push(args);
            die "too few expectedResults: {@expectedResults.elems}"
                if @expectedResults.elems < @receivedArgs.elems;
            @expectedResults[@receivedArgs.elems -1];
        }
    }
    
    testTermFn(makeF("foo", "bar", "baz", 23, 42),
        'x' => "foo",
        `'y' => "bar",
        [`'z', `'x'] => "baz",
        [`'z', y => `'x'] => 23,
        [[y => `'x', 'x' => `'z']] => 42,
    );

    is(@receivedArgs.elems, 5, 'calls the term-fn as many times as there are test-cases');
    is(@receivedArgs[0].perl, \(`'x').perl, 'turns Str key into prepared test-term and applies term-fn to it');
    is(@receivedArgs[1].perl, \(`'y').perl, 'passes TTerm key to term-fn as arg');
    
    subtest({
        is(@receivedArgs[2].perl, \(`'z', `'x').perl, 'passes TTerm elems of Array key to the term-fn as is (1)');

        is(@receivedArgs[3][0].perl, (`'z').perl, 'passes TTerm elems of Array key to the term-fn as is (2)');
        does_ok(@receivedArgs[3][1], TPair, 'passes Pair elems of Array key as TPair Str convert2Lambda(*) to the term-fn / 2nd elem')
            or die;
        is($fst(@receivedArgs[3][1]).perl, '"y"', 'passes Pair elems of Array key as TPair Str convert2Lambda(*) to the term-fn (fst of 2nd elem)');
        is($snd(@receivedArgs[3][1]).perl, (`'x').perl, 'passes Pair elems of Array key as TPair Str convert2Lambda(*) to the term-fn (snd of 2nd elem)');
        
        does_ok(@receivedArgs[4][0], TList, 'passes Array elems of Array key as TList convert2Lambda(*) to the term-fn')
            or die;
        my $e0 = $car(@receivedArgs[4][0]);
        does_ok($e0, TPair, 'passes Array elems of Array key as TList convert2Lambda(*) to the term-fn (1st elem of List)')
            or die;
        is($fst($e0).perl, '"y"',  'passes Array elems of Array key as TList convert2Lambda(*) to the term-fn (fst of 1st elem of List)');
        is($snd($e0).perl, (`'x').perl,  'passes Array elems of Array key as TList convert2Lambda(*) to the term-fn (snd of 1st elem of List)');
        my $e1 = $cadr(@receivedArgs[4][0]);
        does_ok($e1, TPair, 'passes Array elems of Array key as TList convert2Lambda(*) to the term-fn (2nd elem of List)')
            or die;
        is($fst($e1).perl, '"x"',  'passes Array elems of Array key as TList convert2Lambda(*) to the term-fn (fst of 2nd elem of List)');
        is($snd($e1).perl, (`'z').perl,  'passes Array elems of Array key as TList convert2Lambda(*) to the term-fn (snd of 2nd elem of List)');
    }, 'passes elems of an Array key to the term-fn as args');

}, '`&testTermFn` ');

{ # is_eq test for TTerms
    does_ok &is_eq-Term, Callable, 'exports `&is_eq-Term`';
    lives_ok({ is_eq-Term($VarT('x'), $VarT('x')) }, 'can call &is_eq-Term without msg string');
    lives_ok({ is_eq-Term($VarT('x'), $VarT('x'), 'var x equals var x') }, 'can call &is_eq-Term with a msg string');
    
    is_eq-Term($ConstT('c'), $ConstT('c'), '$ConstT("c") equals $ConstT("c")');
    is_eq-Term(`'"c"', $ConstT('c'), 'test-term `"c" equals $ConstT("x")');
    is_eq-Term($ConstT('c'), `'"c"', '$ConstT("x") equals test-term `"c"');
    is_eq-Term(`'"c"', `'"c"', 'test-term `"c" equals test-term `"c"');
}

{ # test the test-terms
    does_ok $testTerms, Any, 'exports `$testTerms`';

    my @ks = $testTerms.keys;
    my @vs = $testTerms.values;
    my $ct = $testTerms.constructionTime;

    diag sprintf('%d test terms (%d keys ttl, avg: %1.1f) / construction time: %s sec ttl, avg: %s ms',
        @vs.elems,
        @ks.elems, @ks.elems.Real / @vs.elems,
        $ct.round(0.01), ($ct * 1000 / @vs.elems).round(1)
    );

    subtest({
        for @vs -> $value {
            my $mainKey = $value.mainKey;
            my $pass = True;
            if $value.Str ne '(ConstT 5)' {   # TODO: add (decimal) number constant literals to grammar
                subtest({
                    my TTerm $term = parseLambda($mainKey);
                    $pass &&= is $mainKey, $Term2srcFull($term), "main key is fully parenthesized lambda expr";
                    $pass &&= is_eq-Term($term, $value, 'parsed main key yields same term as value');
                    for $value.synonyms -> $s {
                        my $sValue = $testTerms.get($s);
                        subtest({
                            $pass &&= cmp_ok($sValue, '===', $value, "...points to same value as main key");
                            $pass &&= lives_ok({ parseLambda($s) }, "...is a valid lambda expr");
                        }, "synonym {$s.perl}");
                    }
                }, "test term with main key {$mainKey.perl}");
                die unless $pass;
            }
        }
    }, 'test-terms');
}

subtest({ # prefix operator ` (for retrieving pre-built test-terms)
    my $x = $VarT('x');
    my $omegaX = $LamT('x', $AppT($x, $x));
    
    is_eq-Term(`'x', $x, 'simple var x from %terms');
    
    is_eq-Term(`'(λx.(x x))', $omegaX, 'omega as fully parenthesized lambda expr');
    is_eq-Term(`'λx.(x x)',   $omegaX, 'omega as lambda expr without surrounding parens');
    is_eq-Term(`'ωX',         $omegaX, 'omega as symbol ωX');
}, 'prefix op ` retrieves...');


# - Util_List -----------------------------------------------------------------

{ # is_eq-List
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

