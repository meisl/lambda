use v6;

use Test;
use Lambda::LambdaGrammar;
use Lambda::LambdaModel;

plan 10;

{ # Term.isEtaRedex
    my $x = λ('x');

    is($x.isEtaRedex, False, "a VarT is not an eta redex");

    my $c = ConstT.new(:value('c'));
    is($c.isEtaRedex, False, "a ConstT is not an eta redex");
    
    my $app1 = AppT.new(:func($x), :arg($c));
    # (x c)
    is($app1.isEtaRedex, False, "an AppT is not an eta redex (arg ConstT)");
    
    my $y = VarT.new(:name<y>);
    is(λ('(x y)').isEtaRedex, False, "an AppT is not an eta redex (func VarT, arg VarT)");
    
    is(λ('((λy.x y) y)').isEtaRedex, False, "an AppT is not an eta redex (func LamT, arg VarT)");
    
    my $lam1 = LamT.new(:var($x), :body($c));
    # (λx.c)
    is($lam1.isEtaRedex, False, "a LamT with body a ConstT is not an eta redex");
    
    is(λ('(λx.x)').isEtaRedex, False, "a LamT with body a VarT is not an eta redex");
    
    my $lam3 = LamT.new(:var($x), :body(AppT.new(:func($x), :arg($c))));
    # (λx.x c)
    is($lam3.isEtaRedex, False, "a LamT with body an AppT where arg is a ConstT is not an eta redex");

    is(λ('(λx.x y)').isEtaRedex, False,
        "a LamT with body an AppT where arg is a VarT other than the lambda's is not an eta redex");

    is(λ('(λx.y x)').isEtaRedex, True,
        "a LamT with body an AppT where arg is a VarT equal to the lambda's IS an eta redex");
}
