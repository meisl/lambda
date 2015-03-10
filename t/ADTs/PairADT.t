use v6;
use Test;
use Test::Util;
use Test::Util_Lambda;


# module under test:
use Lambda::PairADT;

plan 26;


# ->Str -----------------------------------------------------------------------

{ # Pair->Str
    is_properLambdaFn($Pair2Str, 'Pair->Str');
}


# Pair ------------------------------------------------------------------------

{ # ctor Pair
    is_properLambdaFn($Pair, 'Pair');

    doesnt_ok $Pair, TPair,     'Pair', :msg('Pair is NOT a TPair in itself');
    dies_ok { $Pair2Str($Pair) }, "($Pair2Str $Pair) yields error";
    
    my $x;
    $x = $Pair(42, "foo");
    is $Pair2Str($x), '(Pair 42 "foo")',
        "($Pair2Str (Pair 42 \"foo\"))";
    does_ok $x, TPair, "$x";
    is_validLambda $x;

    # can nest 'em:

    $x = $Pair($Pair(1, 2), $Pair("foo", 4));
    is $Pair2Str($x), '(Pair (Pair 1 2) (Pair "foo" 4))',
        "($Pair2Str (Pair (Pair 1 2) (Pair \"foo\" 4)))";
    does_ok $x, TPair, "$x";
    is_validLambda $x;
}

{ # projection fst / Pair->fst
    is_properLambdaFn($Pair2fst, 'Pair->fst');
    ok $fst === $Pair2fst, '$fst is a synonym for $Pair2fst';

    doesnt_ok $Pair2fst, TPair,  'Pair->fst', :msg('Pair->fst is NOT a TPair in itself');
    dies_ok {$Pair2Str($Pair2fst) }, "($Pair2Str $Pair2fst) yields error";

    my $x;
    $x = $Pair(5, 23);
    is $fst($x),  5, "(fst $x)";

    $x = $Pair("foo", 23);
    is $fst($x),  'foo', "(fst $x)";

    $x = $Pair("foo", "bar");
    is $fst($x),  'foo', "(fst $x)";

    $x = $Pair($x, "qumbl");
    is $fst($fst($x)),  'foo', "(fst (fst $x))";
}

{ # projection snd / Pair->snd
    is_properLambdaFn($Pair2snd, 'Pair->snd');
    ok $snd === $Pair2snd, '$snd is a synonym for $Pair2snd';

    doesnt_ok $Pair2snd, TPair,  'Pair->snd', :msg('Pair->snd is NOT a TPair in itself');
    dies_ok {$Pair2Str($Pair2snd) }, "($Pair2Str $Pair2snd) yields error";

    my $x;
    $x = $Pair(5, 23);
    is $snd($x), 23, "(snd $x) -> 23";

    $x = $Pair("foo", 23);
    is $snd($x),  23, "(snd $x) -> 23";

    $x = $Pair("foo", "bar");
    is $snd($x),  'bar', "(snd $x) -> \"bar\"";

    $x = $Pair("qumbl", $x);
    is $snd($snd($x)),  'bar', "(snd (snd $x))";
}
