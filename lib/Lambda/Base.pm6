use v6;

use Lambda::P6Currying;


module Lambda::Base;


role lambda is export {
    has Str:D $.lambda;
    method Str {
        self.?symbol || $!lambda;
    }
    method gist { self.Str }
    #method perl { self.gist }
}

role Definition is export {
    has Str $.symbol;

    submethod BUILD(Str:D :$symbol) {
        $!symbol = $symbol;
    }

    method Str { $!symbol }
}



        #T.perl ~ ' -> ' ~ @!restParams.map(*.perl ~ ' ->') ~ ' ' ~ R.perl;

role Curried {
    method lambdaStr(*@args) {
            '(' ~ self  ~ @args.map( -> $a {' ' ~ ($a.?symbol // $a.?lambda // $a.perl) }) ~ ')'
    }

    method partial(&f, *@args) {
        lambdaFn(Str, self.lambdaStr(@args), &f);
    }
}

sub lambdaStr($self, *@args) {
        '(' ~ $self ~ @args.map( -> $a {' ' ~ ($a.?symbol // $a.?lambda // $a.perl) }) ~ ')'
}

sub lambdaFn(Str $symbol, Str:D $lambdaExpr, &f) is export {
    my $arity = &f.?arity // &f.signature.params.elems;
    if $arity == 0 {
        die "cannot make lambda function with zero parameters: symbol=$symbol, lambdaExpr=$lambdaExpr, &f.signature=" ~ &f.signature.perl ~ ', &f=' ~ &f.perl;
    } else {
        my $out = curry(&f);
        my $lx = $lambdaExpr.substr(0, 1) eq '(' ?? $lambdaExpr !! "($lambdaExpr)";
        $out does lambda($lx);
        $out does Definition(:$symbol)
            if $symbol.defined;
        $out;
    }
}

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
            Str, 'λx.' ~ &f.Str ~ ' (' ~ &g.Str ~ ' x)',
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
            say "inside findFP";
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
constant $pi4o4 is export ::= lambdaFn('π4->4', 'λa.λb.λc.λd.d', -> $a, $b, $c, $d { $d });
