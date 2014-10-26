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
    'Some', 'λx.λsel.sel #true x',
    -> $x {
        my $xStr = $x.?name // $x.?lambda // $x.perl;
        lambdaFn(
            "(Some $xStr)", "λsel.sel #true $xStr",
            -> &sel { &sel($true, $x) }
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
            {   my $v = $m($pi2o2);
                $v ~~ lambda ?? $v !! $v.?name // $v.?lambda // $v.perl;
            },
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
            { '(Some ' ~ $Some2value($m) ~ ')' }
        )
    }
);
