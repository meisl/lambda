use v6;
use Test;
use Test::Util;

use Lambda::Boolean;
use Lambda::MaybeADT;


# module under test:
use Lambda::ListADT;

plan 79;


# functions on List -----------------------------------------------------------

{ # foldl
    is_properLambdaFn($foldl);
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
            is @seen[0][0], 23, "passes initial value to f as 1st arg in first call";
            is @seen[0][1], 'A', "passes current elem to f as 2nd arg";
            is @seen[1][0], 2, "passes last result from f to f as 1st arg in subsequent calls";
            is @seen[1][1], 'B', "passes current elem to f as 2nd arg";
        }, "foldl on non-empty list") or diag 'seen: [ ' ~  @seen.map(*.perl).join(', ') ~ ' ]' and die;
    }
}

# foldr
for ($foldr, $foldr-rec, $foldr-iter) -> $foldr {
    is_properLambdaFn($reverse);
    is_properLambdaFn($foldr);
    is_properLambdaFn($foldr-rec);
    is_properLambdaFn($foldr-iter);
    subtest {
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
    }, "foldr implemented as {$foldr.symbol}: {$foldr.lambda}";
}

{ # reverse
    is_properLambdaFn($reverse);

    is $reverse($nil), $nil, 'reversing the empty list yields the empty list';
    
    my $xs = $cons(23, $nil);
    is $reverse($xs), $xs, 'reversing a singleton list yields the same list';
    
    my $ys = $cons(42, $xs);
    my $ys-reversed = $reverse($ys);
    does_ok $ys-reversed, TList;
    is_validLambda $ys-reversed;
    is $car($ys-reversed), 23, 'first of reversed two-elem list is last of original list';
    is $car($cdr($ys-reversed)), 42, 'second of reversed two-elem list is first of original list';
    
    my $ys-reversed-twice = $reverse($ys-reversed);
    does_ok $ys-reversed-twice, TList;
    is_validLambda $ys-reversed-twice;
    is $ys-reversed-twice, $ys, 'reversing twice gives back original list';
}

{ # length
    is_properLambdaFn($length);

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
    is_properLambdaFn($append);

    my $xs = $nil;
    my $ys = $append($xs, $xs);
    is $is-nil($ys), $true, "appending nil to nil yields nil";

    $xs = $cons(1, $xs);
    $ys = $append($xs, $nil);
    does_ok $ys, TList;
    is_validLambda $ys;
    is $length($ys), 1, "appending nil to a 1-elem list yields a 1-elem list";
    is $car($ys), 1, "...and gives the same list";

    $ys = $append($nil, $xs);
    does_ok $ys, TList;
    is_validLambda $ys;
    is $length($ys), 1, "appending a 1-elem list to nil yields a 1-elem list";
    is $car($ys), 1, "...and gives the same list";

    $xs = $cons(2, $xs);    # [2, 1]
    $ys = $cons(3, $cons(4, $nil)); # [3, 4]
    my $zs = $append($xs, $ys);
    subtest {
        does_ok $zs, TList;
        is_validLambda $zs;
        is $length($zs), 4, "appending a two-elem list to a two-elem list yields a 4-elem list";
        is $car($zs), 2, "1st elem of result";
        is $car($cdr($zs)), 1, "2nd elem of result";
        is $car($cdr($cdr($zs))), 3, "3rd elem of result";
        is $car($cdr($cdr($cdr($zs)))), 4, "4th elem of result";
    }, "appending two two-elem lists" or diag $zs and die;
}

{ # map
    is_properLambdaFn($map);
    is_properLambdaFn($map-foldr);
    is_properLambdaFn($map-rec);
    is_properLambdaFn($map-iter);

    my $xs = $cons(1, $cons(2, $cons(3, $cons(4, $nil))));
    my &f = -> $x { 2*$x };
    for ($map, $map-foldr, $map-rec, $map-iter) -> $map {
        subtest {
            my $ys = $map(&f, $xs);
            is $length($ys), 4, "should have same length after map";
            is $car($ys), 2, "has mapped 1st elem";
            is $cadr($ys), 4, "has mapped 2nd elem";
            is $caddr($ys), 6, "has mapped 3rd elem";
            is $car($cdddr($ys)), 8, "has mapped 4th elem";
        }, "map implemented as $map / {$map.lambda}";
    }
}

{ # filter
    is_properLambdaFn($filter);

    my &isEven = -> $x { if ($x % 2 == 0) { $true } else { $false } };
    my ($xs, $ys);

    $xs = $nil;
    $ys = $filter(&isEven, $nil);
    does_ok $ys, TList;
    is_validLambda $ys;
    is $ys, $nil, 'filtering the empty list yields the empty list';

    $xs = $cons(1, $cons(2, $cons(3, $cons(4, $nil))));
    $ys = $filter(&isEven, $xs);
    does_ok $ys, TList;
    is_validLambda $ys;
    is $length($ys), 2, "should haved filtered out half of them";
    is $car($ys), 2, "found first even";
    is $cadr($ys), 4, "found second even";
}

{ # exists
    is_properLambdaFn($exists);

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

{ # first
    is_properLambdaFn($first);

    my &even = -> $x { if ($x % 2 == 0) { $true } else { $false } };
    my &odd  = -> $x { if ($x % 2 == 1) { $true } else { $false } };
    my &negative = -> $x { if ($x < 0) { $true } else { $false } };

    is $first(&even,     $nil), $None, "first(even) on empty list yields $None";
    is $first(&odd,      $nil), $None, "first(odd) on empty list yields $None";
    is $first(&negative, $nil), $None, "first(negative) on empty list yields $None";

    my $xs = $cons(1, $cons(2, $cons(3, $cons(4, $cons(5, $nil)))));
    is $first(&even,     $xs), $Some(2),  "first(even) yields (Some 2) on $xs";
    is $first(&odd,      $xs), $Some(1),  "first(odd) yields (Some 1) on $xs";
    is $first(&negative, $xs), $None,     "first(negative) yields $None on $xs";

    my @seen = @();
    my &isTwo = -> $x { @seen.push($x); if $x == 2 { $true } else { $false } }
    is $first(&isTwo, $xs), $Some(2),   "first(isTwo) yields (Some 2) one $xs";
    is @seen.elems, 2, "should have stopped after first match";
}
