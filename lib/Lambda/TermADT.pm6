use v6;

use Lambda::Base;
use Lambda::Boolean;

module Lambda::TermADT;
# data Term = VarT name:Str
#           | AppT func:Term arg:Term
#           | LamT var:VarT body:Term
role TTerm is export {
}


# constructors

constant $VarT is export = lambdaFn(
    'VarT', 'λname.λprj.prj #false #false name _',
    -> Str:D $name {
        my $nameStr = $name.perl;
        lambdaFn(
            "(VarT $nameStr)", "λprj.prj #false #false $nameStr _",
            -> &prj { &prj($false, $false, $name, Mu) }
        ) does TTerm;
    }
);

constant $AppT is export = lambdaFn(
    'AppT', 'λfunc.λarg.λprj.prj #false #true func arg',
    -> TTerm:D $func, TTerm:D $arg {
        lambdaFn(
            "(AppT $func $arg)", "λprj.prj #false #true $func $arg",
            -> &prj { &prj($false, $true, $func, $arg) }
        ) does TTerm;
    }
);



# predicates

constant $is-VarT is export = lambdaFn(
    'VarT?', 'λt.t λtag1.λtag0.λ_.λ_._and (not tag1) (not tag0)',
    -> TTerm:D $t {
        $t(-> $tag1, $tag0, $x, $y { $_and($not($tag1), $not($tag0)) })
    }
);

constant $is-AppT is export = lambdaFn(
    'AppT?', 'λt.t λtag1.λtag0.λ_.λ_._and (not tag1) tag0',
    -> TTerm:D $t {
        $t(-> $tag1, $tag0, $x, $y { $_and($not($tag1), $tag0) })
    }
);



# projections

constant $VarT2name is export = lambdaFn(
    'VarT->name', 'λt.if (VarT? t) (t π4->3) (error (~ "cannot apply VarT->name to " (Term->Str t)))',
    -> TTerm:D $t {
        $_if( $is-VarT($t),
            { $t($pi3o4) },
            { die "cannot apply VarT->name to $t" }
        )
    }
);

constant $AppT2func is export = lambdaFn(
    'AppT->func', 'λt.if (AppT? t) (t π4->3) (error (~ "cannot apply AppT->func to " (Term->Str t)))',
    -> TTerm:D $t {
        $_if( $is-AppT($t),
            { $t($pi3o4) },
            { die "cannot apply AppT->func to $t" }
        )
    }
);

constant $AppT2arg is export = lambdaFn(
    'AppT->arg', 'λt.if (AppT? t) (t π4->4) (error (~ "cannot apply AppT->arg to " (Term->Str t)))',
    -> TTerm:D $t {
        $_if( $is-AppT($t),
            { $t($pi4o4) },
            { die "cannot apply AppT->arg to $t" }
        )
    }
);


# ->Str

constant $Term2Str is export = lambdaFn(
    'Term->Str', 'λt.(error "NYI")',
    -> TTerm:D $t { $t.Str }
);
