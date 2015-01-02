use v6;

use Lambda::Base;
use Lambda::Boolean;
use Lambda::ListADT;


# Streams are just lazy TList s


constant $iterate is export = $Y(lambdaFn(
    'iterate', 'λself.λf.λx.λprj.prj #true x (self f (f x))',
    -> &self {
        -> &f, $x {
            lambdaFn(   # must call lambdaFn so the result is curried
                Str, 'λprj.prj #true x (λp.self f (f x) p)',
                -> $prj {
                    $prj(
                        $true,
                        $x,
                        lambdaFn(   # must call lambdaFn so the result is curried
                            Str, 'λp.self f (f x) p',
                            -> $p { &self(&f, &f($x))($p) }
                        ) does TList
                    )
                }
            ) does TList
        }
    }
));
