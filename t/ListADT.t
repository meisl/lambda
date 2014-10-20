use v6;

use Test;
use Test::Util;

use Lambda::Base;
use Lambda::Boolean;
use Lambda::ListADT;

plan 58;

{
    dies_ok { $nil       = 0 },  '$nil is immutable';
    does_ok   $nil,      lambda, '$nil';
    does_ok   $nil,      name,   '$nil';

    dies_ok { $cons      = 0 },  '$cons is immutable';
    does_ok   $cons,     lambda, '$cons';
    does_ok   $cons,     name,   '$cons';

    dies_ok({ $is-nil    = 0 },  '$is-nil is immutable');
    does_ok   $is-nil,   lambda, '$is-nil';
    does_ok   $is-nil,   name,   '$is-nil';

    dies_ok({ $list2str  = 0 },  '$list2str is immutable');
    does_ok   $list2str, lambda, '$list2str';
    does_ok   $list2str, name,   '$list2str';

    dies_ok { $car       = 0 },  '$car is immutable';
    does_ok   $car,      lambda, '$car';
    does_ok   $car,      name,   '$car';

    dies_ok { $cdr       = 0 },  '$cdr is immutable';
    does_ok   $cdr,      lambda, '$cdr';
    does_ok   $cdr,      name,   '$cdr';
}

{
    is $is-nil($nil),   $true, '(nil? nil) -> #true';
    is $nil.Str,        'nil', '$nil.Str';
    is $list2str($nil), 'nil', '(list->str nil) -> "nil"';
    is length($nil), 0, '(length nil) -> 0';
    
    my $xs;
    my $ys;

    
    $xs = $cons($nil, $nil);
    is $xs.Str,        '(cons nil nil)', '(cons nil nil).Str';
    is $list2str($xs), '(cons nil nil)', '(list->str (cons nil nil))';

    is $is-nil($xs), $false, "(nil? $xs) -> $false";
    
    dies_ok( { $xs.car }, '.car should not be a method');
    dies_ok( { $xs.cdr }, '.cdr should not be a method');

    is $car($xs), $nil, "(car $xs) -> $nil";
    is $cdr($xs), $nil, "(cdr $xs) -> $nil";

    is length($xs), 1,  "(length $xs) -> 1";


    $xs = $cons(5, $nil);
    is $xs.Str,        '(cons 5 nil)', '(cons 5 nil).Str';
    is $list2str($xs), '(cons 5 nil)', '(list->str (cons 5 nil))';
    
    is $is-nil($xs), $false, "(nil? $xs) -> #false";

    is $car($xs), 5,    "(car $xs) -> 5";
    is $cdr($xs), $nil, "(cdr $xs) -> nil";

    is length($xs), 1,  "(length $xs) -> 1";


    $ys = $cons('foo', $xs);
    is $ys.Str,     '(cons foo (cons 5 nil))', "$ys.Str";
    is $is-nil($xs), $false, "(nil? $ys) -> $false";

    is $car($ys), "foo", "(car $ys) -> foo";
    is $cdr($ys), $xs,   "(cdr $ys) -> $xs";

    is length($ys), 2,  "(length $ys) -> 2";
}

{ # map
    my $xs = $cons(1, $cons(2, $cons(3, $cons(4, $nil))));
    my &f = -> $x { 2*$x };
    my $ys = map(&f, $xs);
    is length($ys), 4, "should have same length after map";
    is $car($ys), 2, "has mapped 1st elem";
    is $car($cdr($ys)), 4, "has mapped 2nd elem";
    is $car($cdr($cdr($ys))), 6, "has mapped 3rd elem";
    is $car($cdr($cdr($cdr($ys)))), 8, "has mapped 4th elem";
    is cadddr($ys), 8, "has mapped 4th elem";
}

{ # filter
    my $xs = $cons(1, $cons(2, $cons(3, $cons(4, $nil))));
    my &p = -> $x { if ($x % 2 == 0) { $true } else { $false } };

    my $ys = filter(&p, $xs);
    is length($ys), 2, "should haved filtered out half of them";
    is $car($ys), 2, "found first even";
    is cadr($ys), 4, "found second even";
}

{ # exists
    my &even = -> $x { if ($x % 2 == 0) { $true } else { $false } };
    my &odd  = -> $x { if ($x % 2 == 1) { $true } else { $false } };
    my &negative = -> $x { if ($x < 0) { $true } else { $false } };

    is exists(&even,     $nil), $false, "no even exists in empty list";
    is exists(&odd,      $nil), $false, "no odd exists in empty list";
    is exists(&negative, $nil), $false, "no negative exists in empty list";

    my $xs = $cons(1, $cons(2, $cons(3, $cons(4, $cons(5, $nil)))));
    is exists(&even,     $xs), $true,  "even exists in $xs";
    is exists(&odd,      $xs), $true,  "odd exists in $xs";
    is exists(&negative, $xs), $false, "no negative exists in $xs";

    my @seen = @();
    my &isTwo = -> $x { @seen.push($x); if $x == 2 { $true } else { $false } }
    is exists(&isTwo, $xs), $true,   "isTwo exists in $xs";
    is @seen.elems, 2, "should have stopped after first match";
}
