use v6;

use Lambda::Base;
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
            "(Some $vStr)", "λsel.sel #true $vStr",
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
            { $m($pi2o2) },
            { die "cannot get value of None" }
        )
    }
);


# ->Str

constant $Maybe2Str is export = lambdaFn(
    'Maybe->Str', 'λm.(if (None? m) "None" (~ (~ "(Some " (->str (Some->value m))) ")"))',
    -> TMaybe:D $m {
        $_if( $is-None($m),
            { 'None' },
            {
                my $v = $Some2value($m);
                my $vStr = $v.?symbol // $v.?lambda // $v.perl;
                "(Some $vStr)";
            }
        )
    }
);


# functions on Maybe

# Maybe->valueWithDefault

constant $Maybe2valueWithDefault is export = lambdaFn(
    'Maybe->valueWithDefault', 'λm.λdflt.if (None? m) dflt (Some->value m)',
    -> TMaybe:D $m, $dflt {
        $_if( $is-None($m),
            { $dflt },
            { $Some2value($m) }
        )
    }
);
