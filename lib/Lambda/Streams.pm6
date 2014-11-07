use v6;

use Lambda::Base;
use Lambda::Boolean;
use Lambda::ListADT;


# Streams are just lazy TList s


constant $iterate is export = $Y(lambdaFn(
    'iterate', 'λself.λf.λx.λprj.prj #true x (self f (f x))',
    -> &self {
        -> &f, $x {
            ( -> $prj {
                $prj(
                    $true,
                    $x,
                    (-> $p { &self(&f, &f($x))($p) }) does TList
                )
            } ) does TList
        }
    }
));
