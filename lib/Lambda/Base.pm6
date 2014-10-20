use v6;

module Lambda::Base;

# (δ id λx.x)
our $id is export = -> $x {
    $x
} but "id";

# (δ const λx.λy.x)
our $const is export = -> $x {
    -> $y { $x } but ("λy.$x")
} but "const";
