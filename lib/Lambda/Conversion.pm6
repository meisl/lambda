use v6;

use Lambda::BaseP6;
use Lambda::Boolean;
use Lambda::PairADT;
use Lambda::MaybeADT;
use Lambda::ListADT;

module Lambda::Conversion;



sub convertTBool2P6Bool(TBool:D $p) is export {
    $p(True, False);
}

sub convertP6Bool2TBool(Bool:D $p) {
    $p ?? $true !! $false;
}



sub convertTPair2P6Pair(TPair:D $pair) is export {
    Pair.new(:key($fst($pair)), :value($snd($pair)));
}

sub convertP6Pair2TPair(Pair:D (:$key, :$value)) {
    $Pair($key, $value);
}



sub convertTList2P6Array($xs) is export {
    #$foldr(-> $x, $acc { $acc.unshift($x) }, [], $xs);
    $foldl(-> $acc, $x { $acc.push($x) }, [], $xs);
}

sub convertP6Array2TList($array) {
    my $out = $nil;
    for $array.reverse -> $elem { $out = $cons($elem, $out) }
    $out;
}

sub convertP6ArrayToTListOfTPairs(Array $arrayOfarrays) is export {
    convertP6Array2TList( $arrayOfarrays.map({
        die "expected two-elem array but found {$_.perl} instead"
            unless $_.elems == 2;
        $Pair($_[0], $_[1]);
    }) );
}


proto sub convert2Lambda(|) is export {*};

multi sub convert2Lambda(Bool:D   $x) { convertP6Bool2TBool($x) }
multi sub convert2Lambda(Pair:D   $x) { $Pair(convert2Lambda($x.key), convert2Lambda($x.value)) }
multi sub convert2Lambda(         @x) { convertP6Array2TList(@x.map(&convert2Lambda)) }

# deep conversion of Lambda values:
multi sub convert2Lambda(TMaybe:D $x) { case-Maybe($x, None => $None, Some => -> $v { $Some(&convert2Lambda($v)) } ) }
multi sub convert2Lambda(TPair:D  $x) { $Pair(&convert2Lambda($fst($x)), &convert2Lambda($snd($x))) }
multi sub convert2Lambda(TList:D  $x) { $map(&convert2Lambda, $x) }

# any other *non-compound* arg is returned as is
multi sub convert2Lambda(Any:D $x) { $x }

# anything else gives an error:
multi sub convert2Lambda(|args) {
    die "cannot convert to Lambda: {args.perl}";
}
