use v6;

use Test;
use Test::Util;

use Lambda::Base;
use Lambda::Boolean;
use Lambda::ListADT;

plan 89;

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

    dies_ok { $foldl     = 0 },  '$foldl is immutable';
    does_ok   $foldl,    lambda, '$foldl';
    does_ok   $foldl,    name,   '$foldl';

    dies_ok { $reverse   = 0 },  '$reverse is immutable';
    does_ok   $reverse,  lambda, '$reverse';
    does_ok   $reverse,  name,   '$reverse';

    dies_ok { $foldr     = 0 },  '$foldr is immutable';
    does_ok   $foldr,    lambda, '$foldr';
    does_ok   $foldr,    name,   '$foldr';

    dies_ok { $length   = 0 },  '$length is immutable';
    does_ok   $length,  lambda, '$length';
    does_ok   $length,  name,   '$length';

    dies_ok { $filter   = 0 },  '$filter is immutable';
    does_ok   $filter,  lambda, '$filter';
    does_ok   $filter,  name,   '$filter';

    dies_ok { $exists   = 0 },  '$exists is immutable';
    does_ok   $exists,  lambda, '$exists';
    does_ok   $exists,  name,   '$exists';
}

{ # foldl
    {
        my $xs = $nil;
        my @seen = @();
        subtest({
            my $result = $foldl(-> $a, $b { @seen.push([$a, $b].item); @seen.elems * 2 }, 4711, $xs);
            is @seen.elems, 0, "never calls f";
            is $result, 4711, "returns initial value";
        }, "foldl on empty list") or diag 'seen: [ ' ~  @seen.map(*.perl).join(', ') ~ ' ]' and die;
    }

    {
        my $xs = $cons('A', $cons('B', $nil));
        my @seen = @();
        subtest({
            my $result = $foldl(-> $a, $b { @seen.push([$a, $b].item); @seen.elems * 2 }, 23, $xs);
            is @seen.elems, 2, "calls f as many times as there are elements";
            is $result, 4, "returns what f returned last";
            is @seen[0][0], 'A', "passes current elem to f as 1st arg";
            is @seen[0][1], 23, "passes initial value to f as 2nd arg in first call";
            is @seen[1][0], 'B', "passes current elem to f as 1st arg";
            is @seen[1][1], 2, "passes last result from f to f as 2nd arg in subsequent calls";
        }, "foldl on non-empty list") or diag 'seen: [ ' ~  @seen.map(*.perl).join(', ') ~ ' ]' and die;
    }
}

{ # foldr
    {
        my $xs = $nil;
        my @seen = @();
        subtest({
            my $result = $foldr(-> $a, $b { @seen.push([$a, $b].item); @seen.elems * 2 }, 4711, $xs);
            is @seen.elems, 0, "never calls f";
            is $result, 4711, "returns initial value";
        }, "foldr on empty list") or diag 'seen: [ ' ~  @seen.map(*.perl).join(', ') ~ ' ]' and die;
    }

    {
        my $xs = $cons('A', $cons('B', $nil));
        my @seen = @();
        subtest({
            my $result = $foldr(-> $a, $b { @seen.push([$a, $b].item); @seen.elems * 2 }, 23, $xs);
            is @seen.elems, 2, "calls f as many times as there are elements";
            is $result, 4, "returns what f returned last";
            is @seen[0][0], 'B', "passes current elem to f as 1st arg";
            is @seen[0][1], 23, "passes initial value to f as 2nd arg in first call";
            is @seen[1][0], 'A', "passes current elem to f as 1st arg";
            is @seen[1][1], 2, "passes last result from f to f as 2nd arg in subsequent calls";
        }, "foldr on non-empty list") or diag 'seen: [ ' ~  @seen.map(*.perl).join(', ') ~ ' ]' and die;
    }
}

{ # reverse
    is $reverse($nil), $nil, 'reversing the empty list yields the empty list';
    
    my $xs = $cons(23, $nil);
    is $reverse($xs), $xs, 'reversing a singleton list yields the same list';
    
    my $ys = $cons(42, $xs);
    my $ys-reversed = $reverse($ys);
    is $car($ys-reversed), 23, 'first of reversed two-elem list is last of original list';
    is $car($cdr($ys-reversed)), 42, 'second of reversed two-elem list is first of original list';
    
    my $ys-reversed-twice = $reverse($ys-reversed);
    is $ys-reversed-twice, $ys, 'reversing twice gives back original list';
}

{ # length
    my $xs = $nil;
    is $length($xs), 0, "(length $xs) -> 0";

    $xs = $cons(1, $xs);
    is $length($xs), 1, "(length $xs) -> 1";

    $xs = $cons(2, $xs);
    is $length($xs), 2, "(length $xs) -> 2";

    $xs = $cons($xs, $xs); # oh yeah, can put lists into lists!
    is $length($xs), 3, "(length $xs) -> 3";
}

{
    is $is-nil($nil),   $true, '(nil? nil) -> #true';
    is $nil.Str,        'nil', '$nil.Str';
    is $list2str($nil), 'nil', '(list->str nil) -> "nil"';
    
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

    is $length($xs), 1,  "(length $xs) -> 1";


    $xs = $cons(5, $nil);
    is $xs.Str,        '(cons 5 nil)', '(cons 5 nil).Str';
    is $list2str($xs), '(cons 5 nil)', '(list->str (cons 5 nil))';
    
    is $is-nil($xs), $false, "(nil? $xs) -> #false";

    is $car($xs), 5,    "(car $xs) -> 5";
    is $cdr($xs), $nil, "(cdr $xs) -> nil";

    is $length($xs), 1,  "(length $xs) -> 1";


    $ys = $cons('foo', $xs);
    is $ys.Str,     '(cons foo (cons 5 nil))', "$ys.Str";
    is $is-nil($xs), $false, "(nil? $ys) -> $false";

    is $car($ys), "foo", "(car $ys) -> foo";
    is $cdr($ys), $xs,   "(cdr $ys) -> $xs";

    is $length($ys), 2,  "(length $ys) -> 2";
}

{ # map
    my $xs = $cons(1, $cons(2, $cons(3, $cons(4, $nil))));
    my &f = -> $x { 2*$x };
    my $ys = map(&f, $xs);
    is $length($ys), 4, "should have same length after map";
    is $car($ys), 2, "has mapped 1st elem";
    is $car($cdr($ys)), 4, "has mapped 2nd elem";
    is $car($cdr($cdr($ys))), 6, "has mapped 3rd elem";
    is $car($cdr($cdr($cdr($ys)))), 8, "has mapped 4th elem";
    is cadddr($ys), 8, "has mapped 4th elem";
}

{ # filter
    my &isEven = -> $x { if ($x % 2 == 0) { $true } else { $false } };
    is $filter(&isEven, $nil), $nil, 'filtering the empty list yields the empty list';

    my $xs = $cons(1, $cons(2, $cons(3, $cons(4, $nil))));

    my $ys = $filter(&isEven, $xs);
    is $length($ys), 2, "should haved filtered out half of them";
    is $car($ys), 2, "found first even";
    is cadr($ys), 4, "found second even";
}

{ # exists
    my &even = -> $x { if ($x % 2 == 0) { $true } else { $false } };
    my &odd  = -> $x { if ($x % 2 == 1) { $true } else { $false } };
    my &negative = -> $x { if ($x < 0) { $true } else { $false } };

    is $exists(&even,     $nil), $false, "no even exists in empty list";
    is $exists(&odd,      $nil), $false, "no odd exists in empty list";
    is $exists(&negative, $nil), $false, "no negative exists in empty list";

    my $xs = $cons(1, $cons(2, $cons(3, $cons(4, $cons(5, $nil)))));
    is $exists(&even,     $xs), $true,  "even exists in $xs";
    is $exists(&odd,      $xs), $true,  "odd exists in $xs";
    is $exists(&negative, $xs), $false, "no negative exists in $xs";

    my @seen = @();
    my &isTwo = -> $x { @seen.push($x); if $x == 2 { $true } else { $false } }
    is $exists(&isTwo, $xs), $true,   "isTwo exists in $xs";
    is @seen.elems, 2, "should have stopped after first match";
}
