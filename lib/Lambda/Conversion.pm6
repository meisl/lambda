use v6;

use Lambda::Boolean;
use Lambda::PairADT;
use Lambda::ListADT;

module Lambda::Conversion;



sub convertTBool2P6Bool(TBool:D $p) is export {
    $p(True, False);
}

sub convertP6Bool2TBool(Bool:D $p) is export {
    $p ?? $true !! $false;
}



sub convertTPair2P6Pair(TPair:D $pair) is export {
    Pair.new(:key($fst($pair)), :value($snd($pair)));
}

sub convertP6Pair2TPair(Pair:D (:$key, :$value)) is export {
    $Pair($key, $value);
}



sub convertTList2P6Array(TList:D $xs) is export {
    $foldr(-> $x, $acc { $acc.unshift($x) }, [], $xs);
}

sub convertP6Array2TList($array) is export {
    my $out = $nil;
    for $array.reverse -> $elem { $out = $cons($elem, $out) }
    $out;
}

sub convertP6ArrayToTListOfTPairs($arrayOfarrays) is export {
    convertP6Array2TList( $arrayOfarrays.map({
        die "expected two-elem array but found {$_.perl} instead"
            unless $_.elems == 2;
        $Pair($_[0], $_[1]);
    }) );
}


