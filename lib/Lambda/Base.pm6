use v6;

module Lambda::Base;


sub lambdaFn(Str $name, Str:D $lambdaExpr, &f) is export {
    my @p = &f.signature.params;
    if @p == 0 {
        die "cannot make lambda function with zero parameters"
    } else {
        return &f but ($name // $lambdaExpr);
    }
}


our $id is export = lambdaFn(
    'id', 'λx.x',
    -> $x { $x }
);

our $const is export = lambdaFn(
    'const', 'λx.λy.x',
    -> $b { lambdaFn(Str, "λy.$b", -> $y { $b }) }
);
