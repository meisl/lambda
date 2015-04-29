use v6;
use Test;
use Test::Util;
use Test::Util_Lambda;
use Test::Util_List;

use Lambda::Boolean;
use Lambda::MaybeADT;


# module under test:
use Lambda::ListADT;

plan 169;


subtest({ # findFP-inMaybe_dbg ----------------------------------------------------------
    my &step = -> Int $n { $n > 0 ?? $Some($n-1) !! $None };

    is_eq-List($findFP-inMaybe_dbg(&step, 0), [0], 'list with only start value if step-fn returns None on 1st step');
    is_eq-List($findFP-inMaybe_dbg(&step, 1), [0, 1], 'list of values for which step-fn returned a Some (1 step, start value last)');
    is_eq-List($findFP-inMaybe_dbg(&step, 2), [0, 1, 2], 'list of values for which step-fn returned a Some (2 steps, latest value first and start value last)');
    is_eq-List($findFP-inMaybe_dbg(&step, 3), [0, 1, 2, 3], 'list of values for which step-fn returned a Some (3 steps, latest value first and start value last)');
}, 'findFP-inMaybe_dbg');


# ->Str -----------------------------------------------------------------------

{ # List->Str
    is_properLambdaFn $List2Str, 'List->Str';
}


# nil -------------------------------------------------------------------------

{ # ctor nil
    is_properLambdaFn $nil, 'nil';

    does_ok $nil, TList,    'nil', :msg('nil is a TList in itself');
    is $List2Str($nil),     'nil', "($List2Str $nil)";
}

{ # predicate nil?, List2Str, .Str
    is_properLambdaFn $is-nil, 'nil?';

    is $is-nil($nil), $true, '(nil? nil)';
    
    my $xs;
    my $ys;

    $xs = $cons($nil, $nil);
    is $is-nil($xs), $false, "(nil? $xs)";
    is $xs.Str,        '(cons nil nil)', '(cons nil nil).Str"';
    is $List2Str($xs), '(cons nil nil)', "($List2Str (cons nil nil))";


    $xs = $cons(5, $nil);
    is $is-nil($xs), $false, "(nil? $xs)";
    is $xs.Str,        '(cons 5 nil)', '(cons 5 nil).Str';
    is $List2Str($xs), '(cons 5 nil)', "($List2Str (cons 5 nil))";

    $ys = $cons('foo', $xs);
    is $is-nil($xs), $false, "(nil? $ys)";
    is $ys.Str,         '(cons "foo" (cons 5 nil))', "$ys.Str";
    is $List2Str($ys),  '(cons "foo" (cons 5 nil))', "($List2Str $ys)";
}


# cons ------------------------------------------------------------------------

{ # ctor cons
    is_properLambdaFn $cons, 'cons';

    doesnt_ok $cons, TList, 'cons', :msg('cons is NOT a TList in itself');
    dies_ok { $List2Str($cons) }, "($List2Str $cons) yields error";

    my ($xs, $xsStr);

    $xs = $cons($nil, $nil);
    $xsStr = '(cons nil nil)'; # expected
    is $List2Str($xs), $xsStr, "($List2Str $xsStr)";
    does_ok $xs, TList, "$xs";
    is_validLambda($xs);

    $xs = $cons(5, $nil);
    $xsStr = '(cons 5 nil)'; # expected
    is $List2Str($xs), $xsStr, "($List2Str $xsStr)";
    does_ok $xs, TList, "$xs";
    is_validLambda($xs);

    $xs = $cons("foo", $nil);
    $xsStr = '(cons "foo" nil)'; # expected
    is $List2Str($xs), $xsStr, "($List2Str $xsStr)";
    does_ok $xs, TList, "$xs";
    is_validLambda($xs);

    $xs = $cons(42, $cons("bar", $nil));
    $xsStr = '(cons 42 (cons "bar" nil))'; # expected
    is $List2Str($xs), $xsStr, "($List2Str $xsStr)";
    does_ok $xs, TList, "$xs";
    is_validLambda($xs);

    my $ys = $xs; # list of list
    $xs = $cons($xs, $xs);
    $xsStr = '(cons (cons 42 (cons "bar" nil)) (cons 42 (cons "bar" nil)))'; # expected
    is $List2Str($xs), $xsStr, "($List2Str $xsStr)";
    does_ok $xs, TList, "$xs";
    is_validLambda($xs);
}


# the cXr-functions) ----------------------------------------------------------

{ # car
    is_properLambdaFn $car, 'car';

    doesnt_ok $car, TList, 'car', :msg('car is NOT a TList in itself');
    dies_ok {$List2Str($car) }, "($List2Str car) yields error";

    dies_ok({ $car($nil) }, 'car on nil yields error');

    my $xs = $cons(23, $nil);
    is $car($xs), 23, 'car on 1-elem list extracts first elem';

    $xs = $cons(42, $xs);
    is $car($xs), 42, 'car on 2-elem list extracts first elem';
}

{ # cdr
    is_properLambdaFn $cdr, 'cdr';

    doesnt_ok $cdr, TList, 'cdr', :msg('cdr is NOT a TList in itself');
    dies_ok {$List2Str($cdr) }, "($List2Str cdr) yields error";

    dies_ok({ $cdr($nil) }, 'cdr on nil yields error');

    my $xs = $cons(23, $nil);
    is $cdr($xs), $nil, 'cdr on 1-elem list yields nil';

    my $ys = $cons(42, $xs);
    is $cdr($ys), $xs, 'cdr on 2-elem list extracts tail list';
}

{ # caar
    is_properLambdaFn $caar, 'caar';

    dies_ok({ $caar($nil) }, 'caar on nil yields error');

    my $xs = $cons(23, $nil);
    dies_ok({ $caar($xs) }, 'caar on 1-elem list yields error if first elem is not a list');

    $xs = $cons(42, $xs);
    dies_ok({ $caar($xs) }, 'caar on 2-elem list yields error if first elem is not a list');
    
    $xs = $cons($xs, $nil);
    is $caar($xs), 42, 'caar extracts first elem of the list at the first elem (of outer list)';
}

{ # cadr
    is_properLambdaFn $cadr, 'cadr';

    dies_ok({ $cadr($nil) }, 'cadr on nil yields error');

    my $xs = $cons(23, $nil);
    dies_ok({ $cadr($xs) }, 'cadr on 1-elem list yields error');

    $xs = $cons(42, $xs);
    is $cadr($xs), 23, 'cadr extracts 2nd elem (a simple elem)';
    
    my $ys = $cons(5, $cons($xs, $nil));
    is $cadr($ys), $xs, 'cadr extracts 2nd elem (a list)';
}

{ # cdar
    is_properLambdaFn $cdar, 'cdar';

    dies_ok({ $cdar($nil) }, 'cdar on nil yields error');

    my $xs = $cons(23, $nil);
    dies_ok({ $cdar($xs) }, 'cdar on 1-elem list yields error if 1st elem aint a list');

    my $ys = $cons($cons("foo", $xs), $cons("bar", $nil));
    is $cdar($ys), $xs, 'cadr extracts tail of 1st elem';
}

{ # cddr
    is_properLambdaFn $cddr, 'cddr';

    dies_ok({ $cddr($nil) }, 'cddr on nil yields error');

    my $xs = $cons(23, $nil);
    dies_ok({ $cddr($xs) }, 'cddr on 1-elem list yields error');

    $xs = $cons(42, $xs); # xs: (cons 42 (cons 23 nil))
    is $cddr($xs), $nil, 'cddr on 2-elem list yields nil';

    my $ys = $cons($cons("foo", $nil), $cons("bar", $xs));
    is $cddr($ys), $xs, 'cddr extracts tail of tail';
}


{
    is_properLambdaFn $caaar, 'caaar';
    is_properLambdaFn $caadr, 'caadr';
    is_properLambdaFn $cadar, 'cadar';
    is_properLambdaFn $caddr, 'caddr';
    is_properLambdaFn $cdaar, 'cdaar';
    is_properLambdaFn $cdadr, 'cdadr';
    is_properLambdaFn $cddar, 'cddar';
    is_properLambdaFn $cdddr, 'cdddr';

    is_properLambdaFn $caaaar, 'caaaar';
    is_properLambdaFn $caaadr, 'caaadr';
    is_properLambdaFn $caadar, 'caadar';
    is_properLambdaFn $caaddr, 'caaddr';
    is_properLambdaFn $cadaar, 'cadaar';
    is_properLambdaFn $cadadr, 'cadadr';
    is_properLambdaFn $caddar, 'caddar';
    is_properLambdaFn $cadddr, 'cadddr';
    is_properLambdaFn $cdaaar, 'cdaaar';
    is_properLambdaFn $cdaadr, 'cdaadr';
    is_properLambdaFn $cdadar, 'cdadar';
    is_properLambdaFn $cdaddr, 'cdaddr';
    is_properLambdaFn $cddaar, 'cddaar';
    is_properLambdaFn $cddadr, 'cddadr';
    is_properLambdaFn $cdddar, 'cdddar';
    is_properLambdaFn $cddddr, 'cddddr';
}


# functions on List -----------------------------------------------------------

{ # foldl
    is_properLambdaFn $foldl, 'foldl';
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

subtest({ # foldl1
    is_properLambdaFn $foldl1, 'foldl1';

    my $result;
    my @seen = @();
    my &f = -> $a, $b { @seen.push([$a, $b].item); @seen.elems * 2 };
    
    dies_ok { $foldl1(&f, $nil) }, '(foldl1 ... nil) dies';

    @seen = @();
    $result = $foldl1(&f, $cons(23, $nil));
    is @seen.elems, 0, "calls f one time less than nr of elements";
    is $result, 23, 'returns elem for a singleton list';

    @seen = @();
    $result = $foldl1(&f, $cons(42, $cons(23, $cons('A', $nil))));
    is @seen.elems, 2, "calls f one time less than nr of elements";
    is $result, 4, 'returns what f returned last';
    is @seen[0][0], 42,  "passes 1st elem to f as 1st arg in first call";
    is @seen[0][1], 23,  "passes 2nd elem to f as 2nd arg on first call";
    is @seen[1][0], 2,   "passes last result from f to f as 1st arg in subsequent calls";
    is @seen[1][1], 'A', "passes current elem to f as 2nd arg";
}, 'foldl1');

{ # foldr
    is_properLambdaFn $foldr,      'foldr'      or die;
    is_properLambdaFn $foldr-rec,  'foldr-rec'  or die;
    is_properLambdaFn $foldr-iter, 'foldr-iter' or die;

    for ($foldr, $foldr-rec, $foldr-iter) -> $foldr {
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
}

{ # reverse
    is_properLambdaFn $reverse, 'reverse';

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
    is_properLambdaFn $length, 'length';

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
    is_properLambdaFn $append, 'append';

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
    is_properLambdaFn $map,       'map';
    is_properLambdaFn $map-foldr, 'map-foldr';
    is_properLambdaFn $map-rec,   'map-rec';
    is_properLambdaFn $map-iter,  'map-iter';

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
    is_properLambdaFn $filter, 'filter';

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

{ # except = λp.filter (not p)
    is_properLambdaFn $except, 'except';

    my &isEven = -> $x { if ($x % 2 == 0) { $true } else { $false } };
    my ($xs, $ys);

    $xs = $nil;
    $ys = $except(&isEven, $nil);
    does_ok $ys, TList;
    is_validLambda $ys;
    is $ys, $nil, '"excepting" the empty list yields the empty list';

    $xs = $cons(1, $cons(2, $cons(3, $cons(4, $nil))));
    $ys = $except(&isEven, $xs);
    does_ok $ys, TList;
    is_validLambda $ys;
    is $length($ys), 2, "should haved filtered out half of them";
    is $car($ys), 1, "found first non-even";
    is $cadr($ys), 3, "found second non-even";
}

{ # exists
    is_properLambdaFn $exists, 'exists';

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
    is_properLambdaFn $first, 'first';

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
    is @seen.elems, 2, "should stop after first match";
}
