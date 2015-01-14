use v6;

use Lambda::Base;
use Lambda::BaseP6;
use Lambda::Boolean;

module Lambda::MaybeADT;
# data Maybe = None
#            | Some value:_
role TMaybe is export {
}


# constructors

constant $None is export = lambdaFn(
    'None', 'λsel.sel #false _',
    -> &sel { &sel($false, Any) }
) does TMaybe;

constant $Some is export = lambdaFn(
    'Some', 'λv.λsel.sel #true v',
    -> $v {
        my $vStr = $v.?symbol // $v.?lambda // $v.perl;
        lambdaFn(
            Str, "Some $vStr",
            -> &sel { &sel($true, $v) }
        ) does TMaybe
    }
);


# predicates

constant $is-Some is export = lambdaFn(
    'Some?', 'λm.(m π2->1)',
    -> TMaybe:D $m { $m($pi1o2) }
);

constant $is-None is export = lambdaFn(
    'None?', '(B not Some?)',
    -> TMaybe:D $m { $not($m($pi1o2)) }
);


# projections

constant $Some2value is export = lambdaFn(
    'Some->value', 'λm.if (Some? m) (m π2->2) (error "cannot get value of None")',
    -> TMaybe:D $m {
        $_if( $is-Some($m),
            -> $_ { $m($pi2o2) },
            -> $_ { die "cannot get value of None" }
        )
    }
);


# ->Str

constant $Maybe2Str is export = lambdaFn(
    'Maybe->Str', 'λm.(if (None? m) "None" (~ (~ "(Some " (->str (Some->value m))) ")"))',
    -> TMaybe:D $m {
        $_if( $is-None($m),
            -> $_ { 'None' },
            -> $_ { my $v = $Some2value($m);
              my $vStr = $v.?symbol // $v.?lambda // $v.perl;
              "(Some $vStr)";
            }
        )
    }
);


# functions on Maybe

# monadic functions
constant $returnMaybe is export := $Some;

constant $bindMaybe is export = lambdaFn(
    'bindMaybe', 'λm.λf.if (None? m) (K None) (λ_.f (Some->value m))',
    -> TMaybe:D $m, $f {
        $_if( $is-None($m),
            -> $_ { $None },
            -> $_ { $f($Some2value($m)) }
        )
    }
);

constant $liftMaybe is export = lambdaFn(
    'liftMaybe', 'λf.λm.bindMaybe m (B returnMaybe f)',
    -> &f { lambdaFn(
        Str, 'liftMaybe ' ~ (&f.Str // &f.perl),
        -> TMaybe:D $m {
            $bindMaybe($m, -> $x { $returnMaybe(&f($x)) })
        } )
    }
);

constant $lift2Maybe is export = lambdaFn(
    'lift2Maybe', 'λf.λma.λmb.ma `bindMaybe` λa.mb `bindMaybe` λb.returnMaybe (f a b)',
    -> &f { lambdaFn(
        Str, 'lift2Maybe ' ~ (&f.Str // &f.perl),
        -> TMaybe:D $ma, TMaybe:D $mb {
            $bindMaybe($ma, -> $x { $bindMaybe($mb, -> $y { $returnMaybe(&f($x, $y)) } ) })
        } )
    }
);


# Maybe->valueWithDefault
constant $Maybe2valueWithDefault is export = lambdaFn(
    'Maybe->valueWithDefault', 'λm.λdflt.if (None? m) (K dflt) (λ_.Some->value m)',
    -> TMaybe:D $m, $dflt {
        $_if( $is-None($m),
            -> $_ { $dflt },
            -> $_ { $Some2value($m) }
        )
    }
);

# Maybe-lift-in
constant $Maybe-lift-in is export = lambdaFn(
    'Maybe-lift-in', 'λf.λm.if (None? m) (K None) (λ_.f (Some->value m))',
    -> &f { lambdaFn(
        Str, 'Maybe-lift-in ' ~ &f.gist,
        -> TMaybe:D $m {
            $_if( $is-None($m),
                -> $_ { $None },
                -> $_ { &f($Some2value($m)) }
            )
        } )
    }
);

