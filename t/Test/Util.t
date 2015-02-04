use v6;
use Test;

use Lambda::BaseP6;


# modules under test:
use Test::Util;
use Test::Util_Lambda;

plan 1;


{ # does_ok, is_properLambdaFn
    # use ::= to make it immutable
    my $good ::= ( { 42 } but Definition(:symbol<good>) ) but lambda('λx.x');
    my $bad  ::= ( { 23 } but Definition(:symbol<bad>)  ) but lambda('not.a.valid)lambda(term');

    is_properLambdaFn($good);

    # don't know how to test this:
    #is_properLambdaFn($bad);# - should fail with X::Lambda::SyntaxError;
}

todo 'does_ok';
todo 'doesnt_ok';

todo '$contains_ok';
todo '$has_length';