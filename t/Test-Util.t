use v6;

use Test;
use Lambda::Base;
use Lambda::LambdaGrammar;

use Test::Util;

plan 4;

{ # does_ok, is_properLambdaFn
    # use ::= to make it immutable
    my $good ::= (42 but name("good")) but lambda('λx.x');
    my $bad  ::= (23 but name("bad"))  but lambda('not.a.valid)lambda(term');

    is_properLambdaFn($good);

    # don't know how to test this:
    #is_properLambdaFn($bad);# - should fail with X::Lambda::SyntaxError;
}