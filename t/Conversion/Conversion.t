use v6;
use Test;
use Test::Util;
use Test::Util_List;

use Lambda::Boolean;
use Lambda::PairADT;
use Lambda::ListADT;


# modules under test:
use Lambda::Conversion::ListADT-conv;
use Lambda::Conversion::Bool-conv;

plan 33;


{ # convertTBool2P6Bool
    cmp_ok(convertTBool2P6Bool($false), '===', False, 'convertTBool2P6Bool($false)');
    cmp_ok(convertTBool2P6Bool($true),  '===', True,  'convertTBool2P6Bool($true)');
}

{ # convertP6Bool2TBool
    cmp_ok(convertP6Bool2TBool(False), '===', $false, 'convertP6Bool2TBool(False)');
    cmp_ok(convertP6Bool2TBool(True),  '===', $true,  'convertP6Bool2TBool(True)');
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

{ # convertP6Array2TList
    my ($a, $xs);

    $a = [];
    $xs = convertP6Array2TList($a);
    does_ok($xs, TList, "convertP6Array2TList($a)");
    is_eq-List($xs, $a, "convertP6Array2TList($a) equals $a");

    $a = ["foo"];
    $xs = convertP6Array2TList($a);
    does_ok($xs, TList, "convertP6Array2TList($a)");
    is_eq-List($xs, $a, "convertP6Array2TList($a) equals $a");

    $a = ["foo", 5];
    $xs = convertP6Array2TList($a);
    does_ok($xs, TList, "convertP6Array2TList($a)");
    is_eq-List($xs, $a, "convertP6Array2TList($a) equals $a");
}
