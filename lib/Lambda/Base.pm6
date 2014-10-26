use v6;

module Lambda::Base;

role name is export {
    has Str $.name;
    method Str { $!name }
}

role lambda is export {
    has Str:D $.lambda;
    method Str {
        self.?name || $!lambda;
    }
    method gist { $!lambda }
    #method perl { self.gist }
}

sub lambdaFn(Str $name, Str:D $lambdaExpr, &f) is export {
    my @p = &f.signature.params;
    if @p == 0 {
        die "cannot make lambda function with zero parameters"
    } else {
        my $lx = $lambdaExpr.substr(0, 1) eq '(' ?? $lambdaExpr !! "($lambdaExpr)";
        &f does name($name);
        &f does lambda($lx);
        &f;
    }
}


constant $id is export = lambdaFn(
    'id', 'λx.x',
    -> $x { $x }
);
constant $I is export := $id;


constant $const is export = lambdaFn(
    'const', 'λx.λy.x',
    -> $b { lambdaFn(Str, "λy.$b", -> $y { $b }) }
);
constant $K is export := $const;


constant $B is export = lambdaFn(
    'B', 'λf.λg.λx.f (g x)',
    -> &f, &g {
        lambdaFn(
            Str, 'λx.' ~ &f ~ ' (' ~ &g ~ ' x)',
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
            "(C $f)", "λx.λy.$f y x",   # TODO: alpha-convert if necessary
            -> $x, $y { $f($y, $x) }
        );
    }
);
constant $swap-args is export := $C;


constant $W is export = lambdaFn(
    'W', 'λf.λu.f u u',
    -> &f {
        lambdaFn(
            Str, '(W ' ~ (&f ~~ lambda ?? &f.Str !! &f.gist) ~ ')', # TODO: "λu.&f u u", but then alpha-convert if necessary
            -> $u { &f($u, $u) }
        )
    }
);
constant $double-arg is export := $W;


# Turing's Y combinator:
constant $U is export = lambdaFn(
    'U', 'λu.λf.f(u u f)',
    #'U', 'λu.λf.λa..z.f (u u f) a..z', # -> η-reduction...!
    #-> $u { -> &f { -> |args { &f( $u($u)(&f) )(|args) } } }
    -> $u, &f { -> |args { &f( $u($u, &f) )(|args) } }
);

constant $Y is export = lambdaFn(
    'Y', 'U U',
    #'Y', 'W id λu.λf.f(u u f)',
    #'Y', '(λU.U U) λu.λf.f(u u f)',
    #'Y', 'let (U λu.λf.f(u u f)) (U U)',
    #'Y', 'let (U λu.λf.f(u u f)) (λf.f(U U f)',
    #'Y', '(λU.U U) λu.λf.f(u u f)',
    #'Y', '(λu.λf.f(u u f)) (λu.λf.f(u u f))',
    #'Y', 'λf.f((λu.λf.f(u u f)) (λu.λf.f(u u f)) f))',

    #-> &f { &f( $U($U)(&f) ) }
    -> &f {
        lambdaFn(
            &f.?name, '(Y ' ~ (&f ~~ lambda ?? &f.lambda !! &f.gist) ~ ')', # TODO: "λu.&f u u", but then alpha-convert if necessary
            &f( $U($U, &f) )
        )
    }
);


# projections ---------------------------------------------------------

# of 2:
constant $pi1o2 is export = lambdaFn('π2->1', 'λa.λb.a', -> $a, $b { $a });
constant $pi2o2 is export = lambdaFn('π2->2', 'λa.λb.b', -> $a, $b { $b });

# of 3:
constant $pi1o3 is export = lambdaFn('π3->1', 'λa.λb.λc.a', -> $a, $b, $c { $a });
constant $pi2o3 is export = lambdaFn('π3->2', 'λa.λb.λc.b', -> $a, $b, $c { $b });
constant $pi3o3 is export = lambdaFn('π3->3', 'λa.λb.λc.c', -> $a, $b, $c { $c });

# of 4:
constant $pi1o4 is export = lambdaFn('π4->1', 'λa.λb.λc.λd.a', -> $a, $b, $c, $d { $a });
constant $pi2o4 is export = lambdaFn('π4->2', 'λa.λb.λc.λd.b', -> $a, $b, $c, $d { $b });
constant $pi3o4 is export = lambdaFn('π4->3', 'λa.λb.λc.λd.c', -> $a, $b, $c, $d { $c });
constant $pi4o4 is export = lambdaFn('π4->4', 'λa.λb.λc.λd.d', -> $a, $b, $c, $d { $d });
