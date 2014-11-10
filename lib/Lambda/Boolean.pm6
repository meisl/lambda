use v6;

use Lambda::Base;

module Lambda::Boolean;


# data Bool = #false
#           | #true
my role TBool is export {
}

constant $Bool2Str is export = lambdaFn(
    'Bool->Str', 'λp.p "#true" "#false"',
    -> TBool:D $p { $p('#true', '#false') }
);

# "constructors"

constant $true is export = lambdaFn(
    '#true', 'λa.λb.a',
    -> $a, $b { $a }
) does TBool;

constant $false is export = lambdaFn(
    '#false', 'λa.λb.b',
    -> $a, $b { $b }
) does TBool;

# functions on TBool

constant $not is export = lambdaFn(
    'not', 'λp.p #false #true',
    -> TBool:D $p { $p($false, $true) }
);

constant $_if is export = lambdaFn(
    '_if', 'λi.λt.λe.(i t e) _',
    -> TBool:D $cond, &consequence, &alternative {
        $cond(&consequence, &alternative).(Mu)
    }
);

constant $_and is export = lambdaFn(
    '_and', 'λp.λq.p q #false',
    -> TBool:D $p, TBool:D $q {
        $p($q, $false)
    }
);

constant $_or is export = lambdaFn(
    '_or', 'λp.λq.p #true q',
    -> TBool:D $p, TBool:D $q {
        $p($true, $q)
    }
);

