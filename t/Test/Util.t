use v6;
use Test;

use Lambda::BaseP6;


# modules under test:
use Test::Util;
use Test::Util_Lambda;

plan 4;


{ # does_ok, is_properLambdaFn
    # using ::= to make it immutable
    my $bad   ::= ( { 23 } but lambda('not.a.valid)lambda(term') ) but Definition<bad> ;
    my $good1 ::= ( { 42 } but lambda('λx.x')                    ) but Definition<good1>;
    my $good2 ::=   { 11 } but lambda(('λx.x', 'good2'));

    is_properLambdaFn($good1);
    is_properLambdaFn($good1, 'good1');
    is_properLambdaFn($good2);
    is_properLambdaFn($good2, 'good2');

    # TODO: how to test this: `is_properLambdaFn($bad)`- should fail with X::Lambda::SyntaxError;
}

todo 'does_ok';
todo 'doesnt_ok';

todo '$contains_ok';
todo '$has_length';