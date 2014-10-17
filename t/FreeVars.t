use v6;

use Test;
use Lambda::LambdaModel;

plan 65;

{ # VarT.isFree(:$in!)
    my $x = VarT.new(:name<x>);
    my $y = VarT.new(:name<y>);
    my $c = ConstT.new(:value("x"));
    my $app = AppT.new(:func($x), :arg($y));    # '(x y)'
    my $lam = LamT.new(:var($x), :body($app));  # 'λx.x y'

    dies_ok( { $x.isFree($x) }, ".isFree: named arg :in is mandatory");
    dies_ok( { $x.isFree(:in(Term)) }, ".isFree: named arg :in requires defined Term");
    dies_ok({ $c.isFree(:in($x)) }, ".isFree cannot be called on a ConstT");
    dies_ok({ $app.isFree(:in($app)) }, ".isFree cannot be called on an AppT");
    dies_ok({ $lam.isFree(:in($x)) }, ".isFree cannot be called on a LamT");

    is($x.isFree(:in($c)), False, "a var is never free in a ConstT");
    is($x.isFree(:in($x)), True, "a var is free in itself");
    is($x.isFree(:in($y)), False, "a var is not free in another one");
    
    is($x.isFree(:in($app)), True,
        "a var is free if it occurs in the function position of an application");
    is($y.isFree(:in($app)), True,
        "a var is free if it occurs in the argument position of an application");

    is($x.isFree(:in($lam)), False,
        "a var is not free in an abstraction if same as the abstraction's var");
    is($y.isFree(:in($lam)), True,
        "a var is free in an abstraction if different from the abstraction's var");
}

{ # VarT.isFreeUnder(:$binder!, :$in!)
    my $w = VarT.new(:name<w>);
    my $x = VarT.new(:name<x>);
    my $y = VarT.new(:name<y>);
    my $z = VarT.new(:name<z>);
    my $c = ConstT.new(:value("x"));
    my $a1 = AppT.new(:func($x), :arg($y)); # '(x y)'
    my $l = LamT.new(:var($x), :body($a1)); # 'λx.x y'
    my $a2 = AppT.new(:func($l), :arg($z)); # '((λx.x y) z)'
    my $a3 = AppT.new(:func($z), :arg($l)); # '(z (λx.x y))'
    my $a4 = AppT.new(:func($l), :arg($l)); # '((λx.x y) (λx.x y))'

    dies_ok( { $x.isFreeUnder($x)                       }, ".isFreeUnder: named args :binder and :in are mandatory");
    dies_ok( { $x.isFreeUnder(:binder($x))              }, ".isFreeUnder: named arg :in is mandatory");
    dies_ok( { $x.isFreeUnder(               :in($x))   }, ".isFreeUnder: named arg :binder is mandatory");
    dies_ok( { $x.isFreeUnder(:binder($x),   :in(Term)) }, ".isFreeUnder: named arg :in requires a defined Term");
    dies_ok( { $x.isFreeUnder(:binder(VarT), :in($y))   }, ".isFreeUnder: named arg :binder requires a defined VarT");
    dies_ok( { $x.isFreeUnder(:binder($c),   :in($y))   }, ".isFreeUnder: named arg :binder cannot be a ConstT");
    dies_ok( { $x.isFreeUnder(:binder($a1),  :in($y))   }, ".isFreeUnder: named arg :binder cannot be an AppT");
    dies_ok( { $x.isFreeUnder(:binder($l),   :in($y))   }, ".isFreeUnder: named arg :binder cannot be an LamT");
    dies_ok( { $c.isFreeUnder(:binder($x),   :in($y))   }, ".isFreeUnder cannot be called on a ConstT");
    dies_ok( { $a1.isFreeUnder(:binder($x),   :in($y))   }, ".isFreeUnder cannot be called on an AppT");
    dies_ok( { $l.isFreeUnder(:binder($x),   :in($y))   }, ".isFreeUnder cannot be called on a LamT");

    my $msgNeverFree = '.isFreeUnder: never under any binder ';
    is($x.isFreeUnder(:binder($x), :in($c)), False, $msgNeverFree ~ 'in a ConstT');
    is($x.isFreeUnder(:binder($y), :in($c)), False, $msgNeverFree ~ 'in a ConstT');
    is($x.isFreeUnder(:binder($z), :in($c)), False, $msgNeverFree ~ 'in a ConstT');

    is($x.isFreeUnder(:binder($x), :in($x)), False, $msgNeverFree ~ 'in a VarT');
    is($x.isFreeUnder(:binder($y), :in($x)), False, $msgNeverFree ~ 'in a VarT');
    is($x.isFreeUnder(:binder($z), :in($x)), False, $msgNeverFree ~ 'in a VarT');


    # a1: (x y)
    is($x.isFreeUnder(:binder($x), :in($a1)), False);
    is($x.isFreeUnder(:binder($y), :in($a1)), False);
    is($x.isFreeUnder(:binder($z), :in($a1)), False);

    is($y.isFreeUnder(:binder($x), :in($a1)), False);
    is($y.isFreeUnder(:binder($y), :in($a1)), False);
    is($y.isFreeUnder(:binder($z), :in($a1)), False);

    my $msgNeverIfNotOccurring = $msgNeverFree ~ 'if it doesn\'t occur at all';


    # a1: (x y)
    is($w.isFreeUnder(:binder($x), :in($a1)), False, $msgNeverIfNotOccurring ~ ' in app of var to var');
    is($w.isFreeUnder(:binder($y), :in($a1)), False, $msgNeverIfNotOccurring ~ ' in app of var to var');
    is($w.isFreeUnder(:binder($z), :in($a1)), False, $msgNeverIfNotOccurring ~ ' in app of var to var');


    # a2: ((λx.x y) z)
    is($x.isFreeUnder(:binder($x), :in($a2)), False);
    is($x.isFreeUnder(:binder($y), :in($a2)), False);
    is($x.isFreeUnder(:binder($z), :in($a2)), False);

    is($y.isFreeUnder(:binder($x), :in($a2)), True);
    is($y.isFreeUnder(:binder($y), :in($a2)), False);
    is($y.isFreeUnder(:binder($z), :in($a2)), False);

    is($w.isFreeUnder(:binder($x), :in($a2)), False, $msgNeverIfNotOccurring ~ ' in app of lambda to var');
    is($w.isFreeUnder(:binder($y), :in($a2)), False, $msgNeverIfNotOccurring ~ ' in app of lambda to var');
    is($w.isFreeUnder(:binder($z), :in($a2)), False, $msgNeverIfNotOccurring ~ ' in app of lambda to var');


    # a3: (z (λx.x y))
    is($x.isFreeUnder(:binder($x), :in($a3)), False);
    is($x.isFreeUnder(:binder($y), :in($a3)), False);
    is($x.isFreeUnder(:binder($z), :in($a3)), False);

    is($y.isFreeUnder(:binder($x), :in($a3)), True);
    is($y.isFreeUnder(:binder($y), :in($a3)), False);
    is($y.isFreeUnder(:binder($z), :in($a3)), False);

    is($w.isFreeUnder(:binder($x), :in($a3)), False, $msgNeverIfNotOccurring ~ ' in app of var to lambda');
    is($w.isFreeUnder(:binder($y), :in($a3)), False, $msgNeverIfNotOccurring ~ ' in app of var to lambda');
    is($w.isFreeUnder(:binder($z), :in($a3)), False, $msgNeverIfNotOccurring ~ ' in app of var to lambda');


    # a4: ((λx.x y) (λx.x y))
    my $msgNotFreeIfBoundByBoth = $msgNeverFree ~ 'if bound by both, :func and :arg';
    my $msgLam2Lam = ' in app of lambda to lambda';
    is($x.isFreeUnder(:binder($x), :in($a3)), False, $msgNotFreeIfBoundByBoth ~ $msgLam2Lam);
    is($x.isFreeUnder(:binder($y), :in($a3)), False, $msgNotFreeIfBoundByBoth ~ $msgLam2Lam);
    is($x.isFreeUnder(:binder($z), :in($a3)), False, $msgNotFreeIfBoundByBoth ~ $msgLam2Lam);

    is($y.isFreeUnder(:binder($x), :in($a4)), True);
    is($y.isFreeUnder(:binder($y), :in($a4)), False);
    is($y.isFreeUnder(:binder($z), :in($a4)), False);

    is($w.isFreeUnder(:binder($x), :in($a4)), False, $msgNeverIfNotOccurring ~ $msgLam2Lam);
    is($w.isFreeUnder(:binder($y), :in($a4)), False, $msgNeverIfNotOccurring ~ $msgLam2Lam);
    is($w.isFreeUnder(:binder($z), :in($a4)), False, $msgNeverIfNotOccurring ~ $msgLam2Lam);

}