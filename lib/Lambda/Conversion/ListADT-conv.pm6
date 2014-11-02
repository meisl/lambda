use v6;

use Lambda::PairADT;
use Lambda::ListADT;

module Lambda::Conversion::ListADT-conv;


sub convertTList2P6Array(TList:D $xs) is export {
    $foldr(-> $x, $acc { $acc.unshift($x) }, [], $xs);
}

sub convertP6ArrayToTListOfTPairs($arrayOfarrays) is export {
    my $out = $nil;
    for $arrayOfarrays.map({
        die "expected two-elem array but found {$_.perl} instead"
            unless $_.elems == 2;
        $Pair($_[0], $_[1]);
    }).reverse -> $pair { $out = $cons($pair, $out) }
    $out;
}
