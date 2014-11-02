use v6;

use Lambda::Base;
use Lambda::Boolean;

sub convertTBool2P6Bool(TBool:D $p) is export {
    $p(True, False);
}

sub convertP6Bool2TBool(Bool:D $p) is export {
    $p ?? $true !! $false;
}
