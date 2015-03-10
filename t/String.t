use v6;
use Test;
use Test::Util;
use Test::Util_Lambda;

use Lambda::Boolean;


# module under test:
use Lambda::String;

plan 17;



{ # Str-eq?
    is_properLambdaFn($Str-eq, 'Str-eq?');

    is $Str-eq("a", "a"), $true;
    is $Str-eq("the λ calculus", "the λ calculus"), $true;
    is $Str-eq("The λ calculus", "the λ calculus"), $false;

    is $Str-eq("a", "b"), $false;
    is $Str-eq("b", "a"), $false;
    is $Str-eq("a", ""), $false;
    is $Str-eq("", "b"), $false;

    dies_ok({ $Str-eq(Str, 'x') }, 'cannot call it with 1st arg undefined');
    dies_ok({ $Str-eq('x', Str) }, 'cannot call it with 2nd arg undefined');
    dies_ok({ $Str-eq(Str, Str) }, 'cannot call it with both args undefined');

    dies_ok({ $Str-eq(456, 'x') }, 'cannot call it with 1st arg an Int');
    dies_ok({ $Str-eq('x', 456) }, 'cannot call it with 2nd arg an Int');
    dies_ok({ $Str-eq(123, 456) }, 'cannot call it with both args Ints');

    my $partial = $Str-eq('foo');
    is $partial('foo'), $true, 'partial application (1)';
    is $partial('bar'), $false, 'partial application (2)';

    is $partial.lambda, '(Str-eq? "foo")', '.lambda of partially applied Str-eq?';
}

