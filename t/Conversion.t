use v6;

use Test;
use Test::Util;

#use Lambda::Base;
use Lambda::Boolean;
use Lambda::PairADT;
#use Lambda::MaybeADT;
use Lambda::ListADT;
use Lambda::TermADT;

use Lambda::LambdaModel;

plan 18;

{ # convertToP6Bool
    cmp_ok(convertToP6Bool($false), '===', False, 'convertToP6Bool($false)');
    cmp_ok(convertToP6Bool($true),  '===', True,  'convertToP6Bool($true)');
}

{ # convertFromP6Bool
    cmp_ok(convertFromP6Bool(False), '===', $false, 'convertFromP6Bool(False)');
    cmp_ok(convertFromP6Bool(True),  '===', $true,  'convertFromP6Bool(True)');
}

{ # convertToListOfPairs
    my $a;

    $a = [];
    is convertToListOfPairs($a), $nil, 'empty array is mapped to $nil';
    
    $a = [5, [7, "seven"]];
    dies_ok( { convertToListOfPairs($a) }, 'non-array elem in array yields error (1st)');
    
    $a = [[5, "five"], "7"];
    dies_ok( { convertToListOfPairs($a) }, 'non-array elem in array yields error (2nd)');
    
    $a = [[5, "five"], []];
    dies_ok( { convertToListOfPairs($a) }, 'elem in array which is array of 0 yields error');
    
    $a = [[5, "five"], [1]];
    dies_ok( { convertToListOfPairs($a) }, 'elem in array which is array of 1 yields error');
    
    $a = [[5, "five"], [1, 2, 3]];
    dies_ok( { convertToListOfPairs($a) }, 'elem in array which is array of 3 yields error');
    
    $a = [[5, "five"], [1, 2]];
    my $list;
    $list = convertToListOfPairs($a);

    does_ok($list, TList, "convertToListOfPairs({$a.perl})")
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
