use v6;

use Test;
use Lambda::LambdaModel;

plan *;

{
    my $x = VarT.new(:name<x>);
    my $y = VarT.new(:name<y>);
    is($x.hasFreeVar($x), True, "a var is free in itself");
    is($x.hasFreeVar($y), False, "a var is not free in another one");

    my $c = ConstT.new(:value("x"));
    dies_ok({ $x.hasFreeVar($c) }, ".hasFreeVar cannot be called with ConstT arg");
    is($c.hasFreeVar($x), False, "a var is never free in a constant term");
    
    my $app = AppT.new(:func($x), :arg($y));
    dies_ok({ $x.hasFreeVar($app) }, ".hasFreeVar cannot be called with AppT arg");
    is($app.hasFreeVar($x), True,
        "a var is free if it occurs in the function position of an application");
    is($app.hasFreeVar($y), True,
        "a var is free if it occurs in the argument position of an application");

    my $lam = LamT.new(:var($x), :body($app));
    dies_ok({ $x.hasFreeVar($lam) }, ".hasFreeVar cannot be called with LamT arg");
    is($lam.hasFreeVar($x), False,
        "a var is not free in an abstraction if same as the abstraction's var");
    is($lam.hasFreeVar($y), True,
        "a var is free in an abstraction if different from the abstraction's var");

}