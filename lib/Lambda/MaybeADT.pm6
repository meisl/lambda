use v6;

use Lambda::Base;
use Lambda::BaseP6;
use Lambda::Boolean;

use Lambda::P6Currying;


module Lambda::MaybeADT;
# data Maybe = None
#            | Some value:_
role TMaybe is export {
}


# pattern-matching ------------------------------------------------------------

multi sub case-Maybe(TMaybe:D $maybe,
    :None($onNone)!,
    :Some($onSome)!
) is export {
    $maybe($onNone, $onSome);
}

multi sub case-Maybe(|args) {
    die "error applying case-Maybe: " ~ args.perl;
}

# constructors

constant $None is export = lambdaFn(
    'None', 'λonNone.λonSome.onNone',
    -> $onNone, $onSome {
        ($onNone ~~ Block) && ($onNone.signature.arity == 0) 
        ?? $onNone()    # simulate lazy evaluation by passing a thunk (needed only for ctors of arity 0)
        !! $onNone
    }
) does TMaybe;

constant $Some is export = lambdaFn(
    'Some', 'λvalue.λonNone.λonSome.onSome value',
    -> $v {
        my $vStr = $v.?symbol // $v.?lambda // $v.perl;
        lambdaFn(
            Str, "Some $vStr",
            -> $onNone, $onSome { $onSome($v) }
        ) does TMaybe
    }
);


# predicates

constant $is-None is export = lambdaFn(
    'None?', 'λm.m #true (K #false)',
    -> TMaybe:D $m { $m($true, $K1false) }
);

constant $is-Some is export = lambdaFn(
    'Some?', 'λm.m #false (K #true)',
    -> TMaybe:D $m { $m($false, $K1true) }
);


# projections

constant $Some2value is export = lambdaFn(
    'Some->value', 'λm.case m ((Some v) v) (None (error "cannot get value of None"))',
    -> TMaybe:D $m {
        case-Maybe($m,
            None => { die "cannot get value of None" },
            Some => $I
        );
    }
);


# ->Str

# Maybe->Str: Maybe a -> Str
constant $Maybe2Str is export = lambdaFn(
    'Maybe->Str', 'λm.case m (None "None") ((Some v) (~ (~ "(Some " (->str v)) ")"))',
    -> TMaybe:D $m {
        case-Maybe($m,
            None => 'None',
            Some => -> $v { "(Some {$v.?symbol // $v.?lambda // $v.perl})" }
        )
    }
);


# functions on Maybe

# monadic functions
constant $returnMaybe is export := $Some;

# bindMaybe: Maybe a -> (a -> Maybe b) -> Maybe b
constant $bindMaybe is export = lambdaFn(
    'bindMaybe', 'λm.λf.if (None? m) (K None) (λ_.f (Some->value m))',
    -> TMaybe:D $m, $f {
        case-Maybe($m,
            None => $None,
            Some => $f
        )
    }
);

# liftMaybe: (a -> b) -> Maybe a -> Maybe b
constant $liftMaybe is export = lambdaFn(
    'liftMaybe', 'λf.λm.bindMaybe m (B returnMaybe f)',     # λf.(C bindMaybe) (B returnMaybe f)
    -> &f { lambdaFn(
        Str, 'liftMaybe ' ~ (&f.Str // &f.perl),
        -> TMaybe:D $m {
            $bindMaybe($m, -> $x { $returnMaybe(&f($x)) })
        } )
    }
);

# lift2Maybe: (a -> b -> c) -> Maybe a -> Maybe b -> Maybe c
constant $lift2Maybe is export = lambdaFn(
    'lift2Maybe', 'λf.λma.λmb.ma `bindMaybe` λa.mb `bindMaybe` λb.returnMaybe (f a b)', 
    # λf.λma.λmb.ma `bindMaybe` λa.mb `bindMaybe` (returnMaybe ° (f a))
    # λf.λma.λmb.bindMaybe ma ((bindMaybe mb) ° (returnMaybe ° f))
    -> &f { lambdaFn(
        Str, 'lift2Maybe ' ~ (&f.Str // &f.perl),
        -> TMaybe:D $ma, TMaybe:D $mb {
            $bindMaybe($ma, -> $a { $bindMaybe($mb, -> $b { $returnMaybe(&f($a, $b)) } ) })
        } )
    }
);


# Maybe->valueWithDefault
constant $Maybe2valueWithDefault is export = lambdaFn(
    'Maybe->valueWithDefault', 'λm.λdflt.if (None? m) (K dflt) (λ_.Some->value m)',
    -> TMaybe:D $m, $dflt {
        case-Maybe($m,
            None => $dflt,
            Some => $I
        )
    }
);

# Maybe-lift-in: (a -> Maybe b) -> Maybe a -> Maybe b
constant $Maybe-lift-in is export = lambdaFn(
    'Maybe-lift-in', 'C bindMaybe',
    -> &f { lambdaFn(
        Str, 'Maybe-lift-in ' ~ &f.gist,
        -> TMaybe:D $m {
            case-Maybe($m,
                None => $None,
                Some => &f
            )
        } )
    }
);

# findFP-inMaybe: (a -> Maybe b) -> Maybe a -> Maybe b
constant $findFP-inMaybe is export = {
    my $stopCond = -> Mu, $v { $is-None($v) } does lambda('K None?');
    lambdaFn(
        'findFP-inMaybe', 'let ((stopCond (K None?))) λstepFn.B (findFP stopCond (λm.m >>= stepFn)) stepFn',
        -> &stepFunc {
            $B(
                $findFP(
                    $stopCond,
                    #-> TMaybe:D $m { $bindMaybe($m, &stepFunc) }
                    -> TMaybe:D $m { $m($None, &stepFunc) } does lambda("λm.m >>= {&stepFunc.gist}")
                ),
                &stepFunc
            )
        }
    )
}();