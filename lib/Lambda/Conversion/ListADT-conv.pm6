use v6;

use Lambda::PairADT;
use Lambda::ListADT;

module Lambda::Conversion::ListADT-conv;


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
