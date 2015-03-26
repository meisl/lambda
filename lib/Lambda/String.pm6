use v6;
use Lambda::BaseP6;
use Lambda::Boolean;

use Lambda::Conversion;

module Lambda::String;  # tests are in Misc.t


constant $Str-eq is export = lambdaFn(
    'Str-eq?', 'λstr1.λstr2.built-in',
    -> Str:D $str1, Str:D $str2 -->TBool{
        convert2Lambda($str1 eq $str2)
    }
);
