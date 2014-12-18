use v6;

use Test;
use Test::Util;

use Lambda::P6Currying;


plan 13;


{ # binary fn
    constant $g is export = curry(-> Int $x, Str $s -->Str{ $s x $x });

    does_ok($g, Callable, 'curry(...)');
    is $g.arity, 2, "supports method arity";
    does_ok($g.signature, Signature, 'curry(...).signature');

    is $g(3, 'x'), 'xxx', "can call it with expected nr of args";
    my $g3 = $g(3);
    does_ok($g3, Callable, "applying binary fn to one arg yields another Callable");
    is $g3('y'), 'yyy', "can call partially applied binary fn with rest args";

    dies_ok({$g('x', 5)}, "passing two args of wrong type to bin fn throws (immediately)");
    dies_ok({$g('x')}, "passing one arg of wrong type to bin fn throws (immediately)");
    dies_ok({$g3(5)}, "passing one more arg of wrong type to partially applied bin fn throws (immediately)");

    dies_ok({$g(5, 'a', 7)}, "passing three args to bin fn throws (immediately)");
    dies_ok({$g('x', 5, 7)}, "passing three args (of wrong type) to bin fn throws (immediately)");
    dies_ok({$g3('b', 7)}, "passing two args to partially applied bin fn throws (immediately)");
    dies_ok({$g3(9, 7)}, "passing two args (of wrong type) to partially applied bin fn throws (immediately)");


    say $g;
    say $g.WHICH;
    say $g.signature.perl;
    say $g.f.signature.perl;

}

