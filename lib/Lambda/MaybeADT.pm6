use v6;

use Lambda::Base;
use Lambda::BaseP6;
use Lambda::Boolean;

module Lambda::MaybeADT;
# data Maybe = None
#            | Some value:_
role TMaybe is export {
}



# pattern-matching ------------------------------------------------------------

constant $destruct-Maybe is export = lambdaFn(
    'destruct-Maybe', 'λmaybe.λcases.term cases',
    -> TMaybe:D $m, $onNone, $onSome { 
        $m($onNone, $onSome)
    }
);


# constructors

constant $None is export = lambdaFn(
    'None', 'λonNone.λonSome.onNone',
    -> $onNone, $onSome { $onNone }
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
    'Some->value', 'λm.if (Some? m) (m π2->2) (error "cannot get value of None")',
    -> TMaybe:D $m {
        #$_if( $is-Some($m),
        #    -> $_ { $m(Mu, $pi1o1) },
        #    -> $_ {  }
        #)
        $destruct-Maybe($m,
            -> Mu { die "cannot get value of None" },
            $pi1o2
        )(Mu);
    }
);


# ->Str

# Maybe->Str: Maybe a -> Str
constant $Maybe2Str is export = lambdaFn(
    'Maybe->Str', 'λm.(if (None? m) "None" (~ (~ "(Some " (->str (Some->value m))) ")"))',
    -> TMaybe:D $m {
        $destruct-Maybe($m,
            'None',
            -> $v {
              my $vStr = $v.?symbol // $v.?lambda // $v.perl;
              "(Some $vStr)";
            }
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
        $destruct-Maybe($m,
            $None,
            $f
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

# lift2Maybe: (a -> b -> c) -> Maybe a -> Maybe b
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
        $destruct-Maybe($m,
            $dflt,
            $pi1o1
        )
    }
);

# Maybe-lift-in: (a -> Maybe b) -> Maybe a -> Maybe b
constant $Maybe-lift-in is export = lambdaFn(
    'Maybe-lift-in', 'C bindMaybe',
    -> &f { lambdaFn(
        Str, 'Maybe-lift-in ' ~ &f.gist,
        -> TMaybe:D $m {
            $destruct-Maybe($m,
                $None,
                &f
            )
        } )
    }
);

