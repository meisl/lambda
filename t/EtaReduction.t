use v6;

use Test;
use Lambda::LambdaModel;

plan 10;

{ # Term.isEtaRedex
    my $x = VarT.new(:name<x>);

    is($x.isEtaRedex, False, "a VarT is not an eta redex");

    my $c = ConstT.new(:value('c'));
    is($c.isEtaRedex, False, "a ConstT is not an eta redex");
    
    my $app1 = AppT.new(:func($x), :arg($c));
    # (x c)
    is($app1.isEtaRedex, False, "an AppT is not an eta redex (arg ConstT)");
    
    my $y = VarT.new(:name<y>);
    my $app2 = AppT.new(:func($x), :arg($y));
    # (x y)
    is($app2.isEtaRedex, False, "an AppT is not an eta redex (func VarT, arg VarT)");
    
    my $app3 = AppT.new(:func(LamT.new(:var($y), :body(AppT.new(:func($x), :arg($y))))), :arg($y));
    # ((λy.x y) y)
    is($app3.isEtaRedex, False, "an AppT is not an eta redex (func LamT, arg VarT)");
    
    my $lam1 = LamT.new(:var($x), :body($c));
    # (λx.c)
    is($lam1.isEtaRedex, False, "a LamT with body a ConstT is not an eta redex");
    
    my $lam2 = LamT.new(:var($x), :body($x));
    # (λx.x)
    is($lam2.isEtaRedex, False, "a LamT with body a VarT is not an eta redex");
    
    my $lam3 = LamT.new(:var($x), :body(AppT.new(:func($x), :arg($c))));
    # (λx.x c)
    is($lam3.isEtaRedex, False, "a LamT with body an AppT where arg is a ConstT is not an eta redex");

    my $lam4 = LamT.new(:var($x), :body(AppT.new(:func($x), :arg($y))));
    # (λx.x y)
    is($lam4.isEtaRedex, False,
        "a LamT with body an AppT where arg is a VarT other than the lambda's is not an eta redex");

    my $lam5 = LamT.new(:var($x), :body(AppT.new(:func($y), :arg($x))));
    # (λx.y x)
    is($lam5.isEtaRedex, True,
        "a LamT with body an AppT where arg is a VarT equal to the lambda's IS an eta redex");
}