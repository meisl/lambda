use v6;

use Lambda::Base;

module Lambda::Boolean;


my role TBool {
    method Str { bool2str(self) }
}

constant $bool2str is export = lambdaFn(
    'bool2str', 'λp.p "#true" "false"',
    -> TBool:D $p { $p('#true', '#false') }
);

my sub bool2str(TBool:D $self) {
    $bool2str($self);
}

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
        $cond.(&consequence, &alternative).()
    }
);

constant $_and is export = lambdaFn(
    '_and', 'λp.λq.(_if p (λ_.q) (λ_.#false)',
    -> TBool:D $p, TBool:D $q { $_if($p, {$q}, {$false}) }
);

constant $_or is export = lambdaFn(
    '_or', 'λp.λq.(_if p (λ_.#true) (λ_.q)',
    -> TBool:D $p, TBool:D $q { $_if($p, {$true}, {$q}) }
);

