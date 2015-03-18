use v6;
use Lambda::BaseP6;
use Lambda::Boolean;

use Lambda::Conversion::Bool-conv;

module Lambda::String;  # tests are in Misc.t


constant $Str-eq is export = lambdaFn(
    'Str-eq?', 'λstr1.λstr2.built-in',
    -> Str:D $str1, Str:D $str2 -->TBool{
        convertP6Bool2TBool($str1 eq $str2)
    }
);
