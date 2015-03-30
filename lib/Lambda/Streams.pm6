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

constant $map-lazy is export = $Y(-> &self { lambdaFn(
    'map-lazy', 'λf.λxs.error "NYI"',
    -> $f, TList $xs -->TList{
        lambdaFn(
            Str, 'error "NYI"',
            -> $onNil, $onCons {
                case-List($xs,
                    nil => $onNil,
                    cons => -> $hd, $tl { $onCons($f($hd), &self($f, $tl)) }
                );
            }
        ) does TList
    }
)});
