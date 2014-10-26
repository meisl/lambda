use v6;

use Test;
use Test::Util;

use Lambda::PairADT;

plan 32;

{
    is_properLambdaFn($Pair2Str);

    is_properLambdaFn($Pair);

    is_properLambdaFn($Pair2fst);
    ok $fst === $$Pair2fst, '$fst is a synonym for $Pair2fst';
    is_properLambdaFn($Pair2snd);
    ok $snd === $$Pair2snd, '$snd is a synonym for $Pair2snd';
}


{ # Pair->Str
    is $Pair2Str.name, 'Pair->Str', '$Pair2Str.name -> "Pair->Str"';
    is $Pair2Str.Str,  'Pair->Str', '$Pair2Str.Str -> "Pair->Str"';
}

{ # ctor Pair
    is $Pair.name,              'Pair', '$Pair.name -> "Pair"';
    is $Pair.Str,               'Pair', '$Pair.Str -> "Pair"';
    doesnt_ok $Pair, TPair,     'Pair', :msg('Pair is NOT a TPair in itself');
    dies_ok { $Pair2Str($Pair) }, "($Pair2Str $Pair) yields error";
    
    my $x;
    $x = $Pair(42, "foo");
    is $Pair2Str($x), '(Pair 42 "foo")',
        "($Pair2Str (Pair 42 \"foo\")) -> \"(Pair 42 \\\"foo\\\")\"";
    does_ok $x, TPair, "$x";
    is_validLambda $x;

    # can nest 'em:

    $x = $Pair($Pair(1, 2), $Pair("foo", 4));
    is $Pair2Str($x), '(Pair (Pair 1 2) (Pair "foo" 4))',
        "($Pair2Str (Pair (Pair 1 2) (Pair \"foo\" 4))) -> \"(Pair (Pair 1 2) (Pair \\\"foo\\\" 4))\"";
    does_ok $x, TPair, "$x";
    is_validLambda $x;
}

{ # projection fst / Pair->fst
    is $Pair2fst.name,           'Pair->fst', '$Pair2fst.name -> "Pair->fst"';
    is $Pair2fst.Str,            'Pair->fst', '$Pair2fst.Str -> "Pair->fst"';
    doesnt_ok $Pair2fst, TPair,  'Pair->fst', :msg('Pair->fst is NOT a TPair in itself');
    dies_ok {$Pair2Str($Pair2fst) }, "($Pair2Str $Pair2fst) yields error";

    my $x;
    $x = $Pair(5, 23);
    is $Pair2fst($x),  5, "($Pair2fst $x) -> 5";

    $x = $Pair("foo", 23);
    is $Pair2fst($x),  'foo', "($Pair2fst $x) -> \"foo\"";

    $x = $Pair("foo", "bar");
    is $Pair2fst($x),  'foo', "($Pair2fst $x) -> \"foo\"";
}

{ # projection snd / Pair->snd
    is $Pair2snd.name,           'Pair->snd', '$Pair2snd.name -> "Pair->snd"';
    is $Pair2snd.Str,            'Pair->snd', '$Pair2snd.Str -> "Pair->snd"';
    doesnt_ok $Pair2snd, TPair,  'Pair->snd', :msg('Pair->snd is NOT a TPair in itself');
    dies_ok {$Pair2Str($Pair2snd) }, "($Pair2Str $Pair2snd) yields error";

    my $x;
    $x = $Pair(5, 23);
    is $Pair2snd($x), 23, "($Pair2snd $x) -> 23";

    $x = $Pair("foo", 23);
    is $Pair2snd($x),  23, "($Pair2snd $x) -> 23";

    $x = $Pair("foo", "bar");
    is $Pair2snd($x),  'bar', "($Pair2snd $x) -> \"bar\"";
}
