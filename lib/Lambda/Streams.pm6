use v6;

use Lambda::Base;
use Lambda::BaseP6;
use Lambda::Boolean;
use Lambda::ListADT;


# Streams are just lazy TList s


constant $iterate is export = $Y(-> &self { lambdaFn(
    'iterate', 'λself.λf.λx.λonNil.λonCons.onCons x (self f (f x))',
    -> &f, $x {
        lambdaFn(   # must call lambdaFn so the result is curried
            Str, 'λonNil.λonCons.onCons x (λonNil.λonCons.self f (f x) onNil onCons)',
            -> $onNil, $onCons {
                $onCons(
                    $x,
                    lambdaFn(   # let's not η-contract this so the call to &self is lazy
                        Str, 'λonNil.λonCons.self f (f x) onNil onCons',
                        -> $onNil, $onCons { &self(&f, &f($x))($onNil, $onCons) }
                    ) does TList
                )
            }
        ) does TList
    }
)});
