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

constant $const is export = lambdaFn(
    'const', 'λx.λy.x',
    -> $b { lambdaFn(Str, "λy.$b", -> $y { $b }) }
);
