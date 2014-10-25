use v6;

use Test;
use Test::Util;

use Lambda::Base;
use Lambda::Boolean;
use Lambda::ListADT;

plan 149;

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

    dies_ok { $foldr-rec  = 0 },  '$foldr-rec is immutable';
    does_ok   $foldr-rec, lambda, '$foldr-rec';
    does_ok   $foldr-rec, name,   '$foldr-rec';

    dies_ok { $foldr-iter  = 0 },  '$foldr-iter is immutable';
    does_ok   $foldr-iter, lambda, '$foldr-iter';
    does_ok   $foldr-iter, name,   '$foldr-iter';

    dies_ok { $length   = 0 },  '$length is immutable';
    does_ok   $length,  lambda, '$length';
    does_ok   $length,  name,   '$length';

    dies_ok { $append    = 0 },  '$append is immutable';
    does_ok   $append,   lambda, '$append';
    does_ok   $append,   name,   '$append';

    dies_ok { $map       = 0 },  '$map is immutable';
    does_ok   $map,      lambda, '$map';
    does_ok   $map,      name,   '$map';

    dies_ok { $map-foldr       = 0 },  '$map-foldr is immutable';
    does_ok   $map-foldr,      lambda, '$map-foldr';
    does_ok   $map-foldr,      name,   '$map-foldr';

    dies_ok { $map-rec       = 0 },  '$map-rec is immutable';
    does_ok   $map-rec,      lambda, '$map-rec';
    does_ok   $map-rec,      name,   '$map-rec';

    dies_ok { $map-iter       = 0 },  '$map-iter is immutable';
    does_ok   $map-iter,      lambda, '$map-iter';
    does_ok   $map-iter,      name,   '$map-iter';

    dies_ok { $filter   = 0 },  '$filter is immutable';
    does_ok   $filter,  lambda, '$filter';
    does_ok   $filter,  name,   '$filter';

    dies_ok { $first   = 0 },  '$first is immutable';
    does_ok   $first,  lambda, '$first';
    does_ok   $first,  name,   '$first';

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

# foldr
for ($foldr, $foldr-rec, $foldr-iter) -> $foldr {
    diag "foldr implemented as {$foldr.lambda}";
    {
        my $xs = $nil;
        my @seen = @();
        subtest({
            my $result = $foldr(-> $a, $b { say "got $a and $b"; @seen.push([$a, $b].item); @seen.elems * 2 }, 4711, $xs);
            is @seen.elems, 0, "never calls f";
            is $result, 4711, "returns initial value";
        }, "foldr on empty list") or diag 'seen: [ ' ~  @seen.map(*.perl).join(', ') ~ ' ]' and die;
    }

    {
        my $xs = $cons('A', $cons('B', $cons('C', $nil)));
        my @seen = @();
        subtest({
            my $result = $foldr(-> $a, $b { @seen.push([$a, $b].item); @seen.elems * 2 }, 23, $xs);
            is @seen.elems, 3, "calls f as many times as there are elements";
            is $result, 6, "returns what f returned last";
            is @seen[0][0], 'C', "passes current elem to f as 1st arg";
            is @seen[0][1], 23, "passes initial value to f as 2nd arg in first call";
            is @seen[1][0], 'B', "passes current elem to f as 1st arg";
            is @seen[1][1], 2, "passes last result from f to f as 2nd arg in subsequent calls";
            is @seen[2][0], 'A', "passes current elem to f as 1st arg";
            is @seen[2][1], 4, "passes last result from f to f as 2nd arg in subsequent calls";
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

{ # append
    my $xs = $nil;
    my $ys = $append($xs, $xs);
    is $is-nil($ys), $true, "appending nil to nil yields nil";

    $xs = $cons(1, $xs);
    $ys = $append($xs, $nil);
    is $length($ys), 1, "appending nil to a 1-elem list yields a 1-elem list";
    is $car($ys), 1, "...and gives the same list";

    $ys = $append($nil, $xs);
    is $length($ys), 1, "appending a 1-elem list to nil yields a 1-elem list";
    is $car($ys), 1, "...and gives the same list";

    $xs = $cons(2, $xs);    # [2, 1]
    $ys = $cons(3, $cons(4, $nil)); # [3, 4]
    my $zs = $append($xs, $ys);
    subtest {
        is $length($zs), 4, "appending a two-elem list to a two-elem list yields a 4-elem list";
        is $car($zs), 2, "1st elem of result";
        is $car($cdr($zs)), 1, "2nd elem of result";
        is $car($cdr($cdr($zs))), 3, "3rd elem of result";
        is $car($cdr($cdr($cdr($zs)))), 4, "4th elem of result";
    }, "appending two two-elem lists" or diag $zs and die;
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
    is $ys.Str,     '(cons "foo" (cons 5 nil))', "$ys.Str";
    is $is-nil($xs), $false, "(nil? $ys) -> $false";

    is $car($ys), "foo", "(car $ys) -> foo";
    is $cdr($ys), $xs,   "(cdr $ys) -> $xs";

    is $length($ys), 2,  "(length $ys) -> 2";
}

{ # map
    my $xs = $cons(1, $cons(2, $cons(3, $cons(4, $nil))));
    my &f = -> $x { 2*$x };
    for ($map, $map-foldr, $map-rec, $map-iter) -> $map {
        diag "map implemented as $map / {$map.lambda}";
        my $ys = $map(&f, $xs);
        is $length($ys), 4, "should have same length after map";
        is $car($ys), 2, "has mapped 1st elem";
        is $car($cdr($ys)), 4, "has mapped 2nd elem";
        is $car($cdr($cdr($ys))), 6, "has mapped 3rd elem";
        is $car($cdr($cdr($cdr($ys)))), 8, "has mapped 4th elem";
        is cadddr($ys), 8, "has mapped 4th elem";
    }
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

{ # first
    my &even = -> $x { if ($x % 2 == 0) { $true } else { $false } };
    my &odd  = -> $x { if ($x % 2 == 1) { $true } else { $false } };
    my &negative = -> $x { if ($x < 0) { $true } else { $false } };

    is $first(&even,     $nil), $nil, "first(even) on empty list yields empty list";
    is $first(&odd,      $nil), $nil, "first(odd) on empty list yields empty list";
    is $first(&negative, $nil), $nil, "first(negative) on empty list yields empty list";

    my $xs = $cons(1, $cons(2, $cons(3, $cons(4, $cons(5, $nil)))));
    is $first(&even,     $xs), $cons(2, $nil),  "first(even) yields [2] on $xs";
    is $first(&odd,      $xs), $cons(1, $nil),  "first(odd) yields [1] on $xs";
    is $first(&negative, $xs), $nil,    "first(negative) yields [] on $xs";

    my @seen = @();
    my &isTwo = -> $x { @seen.push($x); if $x == 2 { $true } else { $false } }
    is $first(&isTwo, $xs), $cons(2, $nil),   "first(isTwo) yields [2] $xs";
    is @seen.elems, 2, "should have stopped after first match";
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
