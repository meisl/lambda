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

sub case-Maybe(TMaybe:D $instance,
    :None($onNone)!,
    :Some($onSome)!
) is export {
    $instance($onNone, $onSome);
}

#multi sub case-Maybe(|args) {
#    die "error applying case-Maybe: " ~ args.perl;
#}


# constructors

constant $None is export = lambdaFn(
    'None', 'λonNone.λonSome.onNone',
    -> $onNone, $onSome {
        ($onNone ~~ Block) && ($onNone.arity == 0) 
        ?? $onNone()    # simulate lazy evaluation by passing a thunk (needed only for ctors of arity 0)
        !! $onNone
    }
) does TMaybe;

constant $K1None is export = $K1($None);
constant $K2None is export = $K2($None);


constant $Some is export = lambdaFn(
    'Some', 'λvalue.λonNone.λonSome.onSome value',
    -> $v {
        lambdaFn(
            Str, { "(Some {$v.?symbol // $v.?lambda // $v.perl})" },
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
multi sub _liftMaybe(&f, TMaybe:D $ma -->TMaybe) is export {
    #$ma($None, -> $b { $Some(&f($b)) });
    case-Maybe($ma,
        None => $None,
        Some => -> $b { $Some(&f($b)) }
    )
}
multi sub _liftMaybe(&f, Capture:D $fArgs, TMaybe:D $ma -->TMaybe) is export {
    #$ma($None, -> $b { $Some(&f($fArgs|, $b)) });
    case-Maybe($ma,
        None => $None,
        Some => -> $b { $Some(&f(|$fArgs, $b)) }
    )
}



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
            Some => $pi1o1
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

# findFP-inMaybe: (a -> Maybe a) -> a -> Maybe a
constant $findFP-inMaybe is export = {
    my $arbiter = lambdaFn(
        Str, 'λv1.λm2.λnextStep.case m2 ((None (Some v1)) ((Some v2) (nextStep v2)))',
        -> $v1, TMaybe $m2, &nextStep { 
            case-Maybe($m2,
                None => { $Some($v1) }, # simulate lazy eval by passing a thunk (the block)
                Some => &nextStep # once more with value of m2
            )
        }
    );
    lambdaFn(
        'findFP-inMaybe', 'let ((stopCond (K None?))) λstepFn.B (findFP stopCond (λm.m >>= stepFn)) stepFn',
        -> &stepFn {
            my $fpSearch = $findFP($arbiter, &stepFn);
            lambdaFn(
                Str, 'λstart.error "NYI"',
                -> $start {
                    case-Maybe(&stepFn($start),
                        None => $None,  # must return None on 1st step rather than Some(start)
                        Some => $fpSearch
                    )
                }
            )
        }
    )
}();
