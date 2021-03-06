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

our sub case-Str(Str:D $s, &otherwise, :ε($onEpsilon)!) is hidden_from_backtrace is export {
    $s eq '' 
        ?? (($onEpsilon ~~ Block) && ($onEpsilon.arity == 0) 
            ?? $onEpsilon()    # simulate lazy evaluation by passing a thunk (needed only for ctors of arity 0)
            !! $onEpsilon)
        !! &otherwise($s.substr(0, 1), $s.substr(1))
    ;
}


constant $is-SPACE is export = lambdaFn(
    'SPACE?', 'λs.Str-eq " "',
    -> Str:D $s -->TBool{ convert2Lambda($s eq ' ') }
);

constant $is-LF is export = lambdaFn(
    'LF?', 'λs.Str-eq "\n"',
    -> Str:D $s -->TBool{ convert2Lambda($s eq "\n") }
);

constant $is-CR is export = lambdaFn(
    'CR?', 'λs.Str-eq "\r"',
    -> Str:D $s -->TBool{ convert2Lambda($s eq "\r") }
);

constant $is-TAB is export = lambdaFn(
    'TAB?', 'λs.Str-eq "\t"',
    -> Str:D $s -->TBool{ convert2Lambda($s eq "\t") }
);

