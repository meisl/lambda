use v6;

module Lambda::Base;

role name is export {
    has Str $.name;
    method Str { $!name }
}

role lambda is export {
    has Str:D $.lambda;
    method Str {
        self.?name // $!lambda;
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
        return ((&f but name($name)) but lambda($lx));
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
    -> $f {
        lambdaFn(
            "(W $f)", "λu.$f u u",   # TODO: alpha-convert if necessary
            -> $u { $f($u, $u) }
        )
    }
);
constant $double-arg is export := $W;


# Turing's Y combinator:
constant $U is export = lambdaFn(
    'U', 'λu.λx.x(u u x)',
    #'U', 'λu.λx.λz.x (u u x) z',
    #-> $u, $x { -> $z { $x( $u($u, $x) )($z) } }
    -> $u, $x { -> |args { $x( $u($u, $x) )(|args) } }
);

constant $Y is export = lambdaFn(
    'Y', 'U U',
    #'Y', 'W id λu.λx.x(u u x)',
    #'Y', '(λU.U U) λu.λx.x(u u x)',
    #'Y', 'let (U λu.λx.x(u u x)) (U U)',
    #'Y', 'let (U λu.λx.x(u u x)) (λx.x(U U x)',
    #'Y', '(λU.U U) λu.λx.x(u u x)',
    #'Y', '(λu.λx.x(u u x)) (λu.λx.x(u u x))',
    #'Y', 'λx.x((λu.λx.x(u u x)) (λu.λx.x(u u x)) x))',

    #-> $x { $x( $U($U)($x) ) }
    -> $x { $x( $U($U, $x) ) }
);