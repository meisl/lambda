use v6;

use Test;
use Lambda::BaseP6;
use Lambda::Boolean;
use Lambda::ListADT;

module Test::Util_List;


constant $contains_ok is export = lambdaFn(
    'contains_ok', 'λy.λxs.λxsDesc.exists (λe.y === e) xs',
    -> $y, TList:D $xs, Str:D $xsDesc {
        is($exists( -> $e { $e === $y ?? $true !! $false }, $xs), $true, "(contains_ok $y $xsDesc)")
            or diag("searched: $y\n in list: $xs") and False;
    }
);

constant $has_length is export = lambdaFn(
    'has_length', 'λxs.λn.λxsDesc.(eq? n (length xs))',
    -> TList:D $xs, Int:D $n, Str:D $xsDesc {
        is($length($xs), $n, "(eq? $n (length $xsDesc))")
            or diag(" of list: $xs") and False;
    }
);