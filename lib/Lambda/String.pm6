use v6;
use Lambda::BaseP6;
use Lambda::Boolean;

use Lambda::Conversion;

module Lambda::String;  # tests are in Misc.t


constant $Str-eq is export = lambdaFn(
    'Str-eq?', 'λs1.λs2.built-in',
    -> Str:D $s1, Str:D $s2 -->TBool{
        convert2Lambda($s1 eq $s2)
    }
);

constant $Str-ne is export = lambdaFn(
    'Str-ne?', 'λs1.λs2.built-in',
    -> Str:D $s1, Str:D $s2 -->TBool{
        convert2Lambda($s1 ne $s2)
    }
);

constant $Str-concat is export = lambdaFn(
    'Str-concat', 'λs1.λs2.built-in',
    -> Str:D $s1, Str:D $s2 -->Str{
        $s1 ~ $s2
    }
);
