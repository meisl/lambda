use v6;

use Lambda::BaseP6;
use Lambda::Base;

module Lambda::Boolean;


# data Bool = #false
#           | #true
my role TBool is export {
}

# pattern-matching ------------------------------------------------------------

multi sub case-Bool(TBool:D $instance,
    :true($onTrue)!,
    :false($onFalse)!
) is export {
    $instance($onTrue, $onFalse);
}

multi sub case-Bool(|args) {
    die "error applying case-Bool: " ~ args.perl;
}


macro xxx_if_($instance, $then, $else) is export {
    quasi { 
        {{{$instance}}}({{{$then}}},{{{$else}}})
    }
}

sub _if_($instance, $then, $else) is inlinable is export {
    $instance($then, $else);
}

# ->Str -----------------------------------------------------------------------

constant $Bool2Str is export = lambdaFn(
    'Bool->Str', 'λp.p "#true" "#false"',
    -> TBool:D $p { $p('#true', '#false') }
);

# "constructors" --------------------------------------------------------------

constant $true is export = lambdaFn(
    '#true', 'λx.λ_.x',
    -> $onTrue, $onFalse {
        ($onTrue ~~ Block) && ($onTrue.arity == 0) 
        ?? $onTrue()    # simulate lazy evaluation by passing a thunk (needed only for ctors of arity 0)
        !! $onTrue
    }
) does TBool;

constant $false is export = lambdaFn(
    '#false', 'λ_.λx.x',
    -> $onTrue, $onFalse {
        ($onFalse ~~ Block) && ($onFalse.arity == 0) 
        ?? $onFalse()    # simulate lazy evaluation by passing a thunk (needed only for ctors of arity 0)
        !! $onFalse
    }
) does TBool;



constant $K1false is export = $K1($false);
constant $K1true  is export = $K1($true);
constant $K2false is export = $K2($false);
constant $K2true  is export = $K2($true); 


# functions on TBool

constant $not is export = lambdaFn(
    'not', 'λp.p #false #true',
    -> TBool:D $p -->TBool{ $p($false, $true) }
);

constant $_if is export = lambdaFn(
    '_if', 'λi.λt.λe.(i t e) _',
    -> TBool:D $cond, &consequence, &alternative {
        $cond(&consequence, &alternative).(Mu)
    }
);

constant $_and is export = lambdaFn(
    '_and', 'λp.λq.p q #false',
    -> TBool:D $p, TBool:D $q -->TBool{
        $p($q, $false)
    }
);

constant $_or is export = lambdaFn(
    '_or', 'λp.λq.p #true q',
    -> TBool:D $p, TBool:D $q -->TBool{
        $p($true, $q)
    }
);

constant $_eqv is export = lambdaFn(
    '_eqv', 'λp.λq.p q (not q)',
    -> TBool:D $p, TBool:D $q -->TBool{
        $p($q, $not($q))
    }
);

constant $_xor is export = lambdaFn(
    '_xor', 'λp.λq.p (not q) q',
    -> TBool:D $p, TBool:D $q -->TBool{
        $p($not($q), $q)
    }
);

