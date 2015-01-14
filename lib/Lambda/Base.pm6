use v6;
use Lambda::BaseP6;

module Lambda::Base;


constant $id is export = lambdaFn(
    'id', 'λx.x',
    -> $x { $x }
);
constant $I is export := $id;


constant $const is export = lambdaFn(
    'const', 'λx.λy.x',
    -> $b { lambdaFn(Str, 'λy.' ~ ($b.?symbol // $b.?lambda // $b.perl), -> $y { $b }) }
);
constant $K is export := $const;


constant $B is export = lambdaFn(
    'B', 'λf.λg.λx.f (g x)',
    -> &f, &g {
        lambdaFn(
            Str, 'λx.' ~ &f.gist ~ ' (' ~ &g.gist ~ ' x)',   # TODO: make sure x doesn't get captured
            -> $x { &f(&g($x)) }
        )
    }
);
constant $compose is export := $B;
# B B
# (λf.λg.λx.f (g x)) (λf.λg.λx.f (g x))
# λf.λx.(λg.λh.λy.g (h y)) (f x)
# λf.λx.λh.λy.f x (h y)
#
# B B f x h
# (λx.λh.λy.f x (h y)) x h
# (λh.λy.f x (h y)) h
# λy.f x (h y)


constant $C is export = lambdaFn(
    'C', 'λf.λx.λy.f y x',
    -> $f {
        lambdaFn(
            Str, "(C $f)",
            -> $x, $y { $f($y, $x) }
        );
    }
);
constant $swap-args is export := $C;


constant $W is export = lambdaFn(
    'W', 'λf.λu.f u u',
    -> &f {
        lambdaFn(
            Str, '(W ' ~ (&f.?lambda // &f.gist) ~ ')', # TODO: "λu.&f u u", but then alpha-convert if necessary
            -> $u { &f($u, $u) }
        )
    }
);
constant $double-arg is export := $W;


my sub recFnSymbol(&f) {
    &f.?symbol // Str
}

my sub recFnLambda(&f) {
    '(Y ' ~ (&f.?lambda // &f.gist) ~ ')' # TODO: "λu.&f u u", but then alpha-convert if necessary
}

# Turing's Y combinator:
constant $Y is export = -> $U { lambdaFn(
    'Y', '((λU.U U) λu.λf.f(u u f))',
    #'Y', 'let (U λu.λf.f(u u f)) (U U)',
    #'Y', 'let (U λu.λf.f(u u f)) (λf.f(U U f))',
    -> &f {
        #say '(Y ' ~ &f.Str ~ ')';
        lambdaFn(
            recFnSymbol(&f), recFnLambda(&f),
            &f( $U($U, &f) )
        )
    }
) }( -> $u, &f { -> |args { &f( $u($u, &f) )(|args) } } );
#) }( -> $u, &f { say "u"; &f( $u($u, &f) ) } );


# fixed-point search ----------------------------------------------------------

# starting at $start, returns the first fixed-point of &method
# wrt. to end-condition `predicate`,
# ie. the first x st. (predicate x (&method x)) == True
# where "===" is the default end-condition.
# ...or diverges if there is none...
constant $findFP is export = $Y(lambdaFn(
    'findFP', 'λself.λp.λf.λstart.let ((next (f start)) (done (p start next))) (if done start (self f next p))',
    -> &self {
        -> &predicate, &f, $start {
            #say "inside findFP: "  ~ $start;
            my $next = &f($start);
            my $done = &predicate($start, $next);    # TODO: move findFP out of Base.pm6, st. dependency on Boolean.pm6 is made clear
            if $done(True, False) { # TODO: once findFP is moved out of Base.pm6: implement using $_if
                $start;
            } else {
                &self(&predicate, &f, $next);
            }
        }
    }
));


# projections ---------------------------------------------------------

# of 2:
constant $pi1o2 is export = lambdaFn('π2->1', 'λx.λ_.x', -> $x, Mu { $x }); # K     = L I = B K I = λx.K (I x) = λx.K x = λx.λ_.x
constant $pi2o2 is export = lambdaFn('π2->2', 'λ_.λx.x', -> Mu, $x { $x }); # K I

# of 3:
constant $pi1o3 is export = lambdaFn('π3->1', 'λx.λ_.λ_.x', -> $x, Mu, Mu { $x });  # L π2->1  =  B K π2->1  =  λx.K (π2->1 x)  =  λx.(K (K x)) = λx.(K (λ_.x)) = λx.λ_.λ_.x
constant $pi2o3 is export = lambdaFn('π3->2', 'λ_.λx.λ_.x', -> Mu, $x, Mu { $x });  # K π2->1  =  K K
constant $pi3o3 is export = lambdaFn('π3->3', 'λ_.λ_.λx.x', -> Mu, Mu, $x { $x });  # K π2->2  =  K (K I)

# of 4:
constant $pi1o4 is export = lambdaFn('π4->1', 'λx.λ_.λ_.λ_.x', -> $x, Mu, Mu, Mu { $x });   # L π3->1   =  L (L (L I))
constant $pi2o4 is export = lambdaFn('π4->2', 'λ_.λx.λ_.λ_.x', -> Mu, $x, Mu, Mu { $x });   # K π3->1   =  K (L (L I))
constant $pi3o4 is export = lambdaFn('π4->3', 'λ_.λ_.λx.λ_.x', -> Mu, Mu, $x, Mu { $x });   # K π3->2   =  K (K (L I))
constant $pi4o4 is export = lambdaFn('π4->4', 'λ_.λ_.λ_.λx.x', -> Mu, Mu, Mu, $x { $x });   # K π3->3   =  K (K (K I))



constant $apply-χ-more = lambdaFn(
    'apply-χ-more', 'λf.λa.λn.n (λg.g a) f',
    -> $f, $a, $n {
        my $apply-to-const = lambdaFn('apply-to-const', 'λc.λg.g c', -> $c, $g { $g($c) });
        $n($apply-to-const($a), $f)
    }
);


constant $eq-pi2 = lambdaFn(
    'eq-π2?', 'λp.λq.p q (q p #true)',
    -> $p, $q {
        my $true  = $K;
        $p($q, $q($p, $true));
    }
);

constant $eq-pi3 = lambdaFn(
    'eq-π3?', 'asdf',
    -> $p, $q {
        my $true  = $K;
        my $false = $K($I);

        my $p-first = $q($true, $false, $false);
        my $q-other = $eq-pi2($p($_), $q($_));
        my $p-other = $q($false, $q-other, $q-other);
        $p($p-first, $p-other, $p-other);
    }
)