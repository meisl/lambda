use v6;

use Test;
use Test::Util;

use Lambda::P6Currying;


plan 17;


{ # binary fn
    my $g ::= curry(-> Int $x, Str $s -->Str{ $s x $x });
    $g.f does role {
        method onPartialApp($self, *@as) {
            #exit;
        }
    }

    does_ok($g, Callable, 'curry(...)');
    is $g.arity, 2, "unapplied bin fn has arity 2";

    is $g(3, 'x'), 'xxx', "can call it with expected nr of args";
    my $g3 = $g(3);
    does_ok($g3, Callable, "applying binary fn to one arg yields another Callable");
    is $g3.arity, 1, "bin fn applied to 1 arg yields fn of arity 1";

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
}


{ # ternary fn
    my @seen = @();

    my $g ::= curry(-> Int $a0, Str $a1, Int $a2 -->Str{ @seen.push(($a0, $a1, $a2).tree); "@ call {@seen.elems}: (" ~ @seen[*-1].map(*.perl).join(', ') ~ ")" });
    is $g.arity, 3, "unapplied ternary fn has arity 3";
    #say $g(1, "two", 3);
    #say $g(2, "three", 4);

    my $g1 = $g(1);
    is $g1.arity, 2, "ternary fn applied to 1 arg yields fn of arity 2";

    my $g1_two = $g1("two");
    is $g1_two.arity, 1, "ternary fn applied to 1 arg and then another arg yields fn of arity 1";

    my $g1two = $g(1, "two");
    is $g1two.arity, 1, "ternary fn applied to 2 args yields fn of arity 1";

}
