use v6;
use Lambda::BaseP6;
use Lambda::Boolean;

use Lambda::Conversion::Bool-conv;

module Lambda::String;


constant $Str-eq is export = lambdaFn(
    'Str-eq?', 'not available',
    -> Str:D $s {
        lambdaFn(
            Str, "Str-eq? {$s.perl}",
            -> Str:D $t -->TBool{
                convertP6Bool2TBool($s eq $t)
            }
        )
    }
);
