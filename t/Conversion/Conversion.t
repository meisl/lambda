use v6;
use Test;
use Test::Util;
use Test::Util_List;    # Note: DO NOT use is_eq-List here since this in turn uses Conversion...!

use Lambda::Boolean;
use Lambda::PairADT;
use Lambda::MaybeADT;
use Lambda::ListADT;
use Lambda::TermADT;


# modules under test:
use Lambda::Conversion;

plan 48;


{ # convert Pairs
    my $tPair1 = $Pair(5, "seven");
    cmp_ok(convert2Lambda($tPair1), '===', $tPair1, '"converting" a TPair to a TPair returns the very same thing');
    my $p6Pair1 = convertTPair2P6Pair($tPair1);
    cmp_ok($p6Pair1.key,    '===', 5,       "$tPair1 converted to {$p6Pair1.perl} (.key)");
    cmp_ok($p6Pair1.value,  '===', "seven", "$tPair1 converted to {$p6Pair1.perl} (.value)");


    my $tPair2 = convert2Lambda($p6Pair1);
    cmp_ok($fst($tPair2),   '===', 5,       "{$p6Pair1.perl} converted back to $tPair2 (fst)");
    cmp_ok($snd($tPair2),   '===', "seven", "{$p6Pair1.perl} converted back to $tPair2 (snd)");

    my $p6Pair2 = Pair.new(key => 42, value => 'twenty-three');
    my $tPair3 = convert2Lambda($p6Pair2);
    cmp_ok($fst($tPair3),   '===', 42,              "{$p6Pair2.perl} converted to $tPair3 (fst)");
    cmp_ok($snd($tPair3),   '===', "twenty-three",  "{$p6Pair2.perl} converted to $tPair3 (snd)");

    my $p6Pair3 = convertTPair2P6Pair($tPair3);
    cmp_ok($p6Pair3.key,    '===', 42,              "$tPair3 converted back to {$p6Pair3.perl} (.key)");
    cmp_ok($p6Pair3.value,  '===', "twenty-three",  "$tPair3 converted back to {$p6Pair3.perl} (.value)");
}


{ # convert Bools
    cmp_ok(convertTBool2P6Bool($false), '===', False, 'convertTBool2P6Bool($false)');
    cmp_ok(convertTBool2P6Bool($true),  '===', True,  'convertTBool2P6Bool($true)');

    cmp_ok(convert2Lambda(False), '===', $false, 'convert2Lambda(False)');
    cmp_ok(convert2Lambda(True),  '===', $true,  'convert2Lambda(True)');
}

{ # convertP6ArrayToTListOfTPairs
    my $a;

    $a = [];
    is convertP6ArrayToTListOfTPairs($a), $nil, 'empty array is mapped to $nil';
    
    $a = [5, [7, "seven"]];
    dies_ok( { convertP6ArrayToTListOfTPairs($a) }, 'non-array elem in array yields error (1st)');
    
    $a = [[5, "five"], "7"];
    dies_ok( { convertP6ArrayToTListOfTPairs($a) }, 'non-array elem in array yields error (2nd)');
    
    $a = [[5, "five"], []];
    dies_ok( { convertP6ArrayToTListOfTPairs($a) }, 'elem in array which is array of 0 yields error');
    
    $a = [[5, "five"], [1]];
    dies_ok( { convertP6ArrayToTListOfTPairs($a) }, 'elem in array which is array of 1 yields error');
    
    $a = [[5, "five"], [1, 2, 3]];
    dies_ok( { convertP6ArrayToTListOfTPairs($a) }, 'elem in array which is array of 3 yields error');
    
    $a = [[5, "five"], [1, 2]];
    my $list;
    $list = convertP6ArrayToTListOfTPairs($a);

    does_ok($list, TList, "convertP6ArrayToTListOfTPairs({$a.perl})")
        or diag "output: $list / {$list.perl}";
    is($length($list), $a.elems, "output has as many elems as input")
        or diag "input: {$a.perl} \noutput: $list / {$list.perl}";

    my $elem;
    
    $elem = $car($list);
    does_ok($elem, TPair, "(car $list)")
        or diag "1st elem: {$elem.perl}";
    cmp_ok($fst($elem), '===', $a[0][0], "1st elem's [0] is fst in 1st pair")
        or  diag "1st elem: {$elem.perl}";
    cmp_ok($snd($elem), '===', $a[0][1], "1st elem's [1] is snd in 1st pair")
        or  diag "1st elem: {$elem.perl}";
    
    $elem = $cadr($list);
    does_ok($elem, TPair, "(cadr $list)")
        or diag "2nd elem: : {$elem.perl}";
    cmp_ok($fst($elem), '===', $a[1][0], "2nd elem's [0] is fst in 2nd pair")
        or  diag "2nd elem: {$elem.perl}";
    cmp_ok($snd($elem), '===', $a[1][1], "2nd elem's [1] is snd in 2nd pair")
        or  diag "2nd elem: {$elem.perl}";
}

{ # convertTList2P6Array
    my ($xs, $a);

    $xs = $nil;
    $a = convertTList2P6Array($xs);
    does_ok($a, Array, "convertTList2P6Array($xs)");
    is($a.elems, 0, "convertTList2P6Array($xs).elems")
        or diag(" in: $xs\nout: {$a.perl}");

    $xs = $cons(5, $nil);
    $a = convertTList2P6Array($xs);
    does_ok($a, Array, "convertTList2P6Array($xs)");
    is($a.elems, 1, "convertTList2P6Array($xs).elems")
        or diag(" in: $xs\nout: {$a.perl}");
    is($a[0], 5, "convertTList2P6Array($xs).[0]")
        or diag(" in: $xs\nout: {$a.perl}");

    $xs = $cons("foo", $cons(5, $nil));
    $a = convertTList2P6Array($xs);
    does_ok($a, Array, "convertTList2P6Array($xs)");
    is($a.elems, 2, "convertTList2P6Array($xs).elems")
        or diag(" in: $xs\nout: {$a.perl}");
    is($a[0], 'foo', "convertTList2P6Array($xs).[0]")
        or diag(" in: $xs\nout: {$a.perl}");
    is($a[1], 5, "convertTList2P6Array($xs).[1]")
        or diag(" in: $xs\nout: {$a.perl}");
}

{ # converting P6 Arrays/Lists to TLists - Note: DO NOT use is_eq-List here since this in turn uses Conversion...!
    subtest({
        my $xs = convert2Lambda([]);
        $has_length($xs, 0);
    }, 'conversion of an empty array to a TList');

    subtest({
        my $xs = convert2Lambda(["foo"]);
        $has_length($xs, 1);
        my $e0 = $car($xs);
        cmp_ok($e0, '===', "foo", '1st elem');
    }, 'conversion of an array of simple types to a TList (1 elem)');

    subtest({
        my $xs = convert2Lambda(["foo", 5]);
        $has_length($xs, 2);
        my $e0 = $car($xs);
        cmp_ok($e0, '===', "foo", '1st elem');
        my $e1 = $cadr($xs);
        cmp_ok($e1, '===', 5, '2nd elem');
    }, 'conversion of an array of simple types to a TList (2 elems)');

    subtest({
        my $x = $VarT('x');
        my $y = $VarT('y');
        my $xs = convert2Lambda([z => $x, x => $y]);
        $has_length($xs, 2);
        my $e0 = $car($xs);
        does_ok $e0, TPair, '1st elem';
        cmp_ok($fst($e0), '===', "z", 'fst of 1st elem');
        cmp_ok($snd($e0), '===', $x,  'snd of 1st elem');
        my $e1 = $cadr($xs);
        does_ok $e1, TPair, '2nd elem';
        cmp_ok($fst($e1), '===', "x", 'fst of 2nd elem');
        cmp_ok($snd($e1), '===', $y,  'snd of 2nd elem');
    }, 'deep conversion of an array of pairs to a TList of TPair s (2 elems)');

    subtest({
        my $x = $VarT('x');
        my $y = $VarT('y');
        my $xs = convert2Lambda([['z', $x], x => $y]);
        $has_length($xs, 2);
        my $e0 = $car($xs);
        does_ok $e0, TList, '1st elem';
        cmp_ok($car($e0), '===', "z", 'car of 1st elem');
        cmp_ok($cadr($e0), '===', $x,  'cadr of 1st elem');
        my $e1 = $cadr($xs);
        does_ok $e1, TPair, '2nd elem';
        cmp_ok($fst($e1), '===', "x", 'fst of 2nd elem');
        cmp_ok($snd($e1), '===', $y,  'snd of 2nd elem');
    }, 'deep conversion of an array of an array and a pair to a TList (2 elems)');
}


{ # (deep) conversion of TMaybe s
    my TMaybe $m;
    
    $m = $None;
    cmp_ok(convert2Lambda($m), '===', $m, 'None -> None');

    $m = $Some($None);
    is(convert2Lambda($m), $m, '(Some None) -> (Some None)');

    my $x = $VarT('x');
    $m = $Some($x => [5, 'seven']);
    my $actual = convert2Lambda($m);
    my $expectedStr = '(Some (Pair (VarT "x") (cons 5 (cons "seven" nil))))';
    my $msg = "(Some (`'x' => [5, \"seven\"]) -> $expectedStr";
    my sub fail {
        diag("expected: $expectedStr\n     got: $actual") and False;
    }
    case-Maybe($actual,
        None => { ok(False, $msg) or fail },
        Some => -> $actualV {
            does_ok($actualV, TPair) or fail;
            cmp_ok($fst($actualV), '===', $x, $msg) or fail;
            my $list = $snd($actualV);
            does_ok($list, TList) or fail;
            $has_length($list, 2);
            my $e0 = $car($list);
            cmp_ok($e0, '===', 5, $msg) or fail;
            my $e1 = $cadr($list);
            cmp_ok($e1, '===', "seven", $msg) or fail;
        }
    );
}
