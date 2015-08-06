#!nqp
use testing;

use L::runtime;


plan(15);


{ # delayMemo / force

    my $n := 0;
    my $block   := { $n := $n + 1; };
    my $delayed := delayMemo($block);

    is($n, 0, 'block not executed yet');
    is(force($delayed), 1, 'block executed once when calling force on delayed block for the 1st time');
    is(force($delayed), 1, 'calling force on delayed block again yields same value as 1st time');
    is(force($block),   2, 'block executed twice when calling force on block');
    is(force($block),   3, 'block executed thrice when calling force on block again');
    is(force($delayed), 1, 'calling force on delayed block yet again yields same value as 1st time');
}


{ # sublist
    my @a := [1,2,3,4,5];
    my @b := sublist(@a, 3);

    is(nqp::elems(@a), 5, 'original list untouched by sublist');
    is(nqp::elems(@b), 2, 'sublist(.., 3) omits 3 elems');
    is(@b[0], @a[3], 'sublist(.., 3), 1st elem left');
    is(@b[1], @a[4], 'sublist(.., 3), 2nd elem left');

    is(nqp::elems(sublist([], 0)), 0, 'sublist([], 0)');

    @a := [1];
    @b := sublist(@a, 0);
    is(nqp::elems(@b), 1,   'sublist([1], 0) yields same list (a)');
    is(@b[0], @a[0],        'sublist([1], 0) yields same list (b)');

    @b := sublist(@a, 1);
    is(nqp::elems(@b), 0,   'sublist([1], 1) yields empty list');

    @b := sublist(@a, 2);
    is(nqp::elems(@b), 0,   'sublist([1], 2) yields empty list');
}


done();
