use v6;

use Test;
use Test::Util;

use Lambda::Boolean;
use Lambda::MaybeADT;
use Lambda::ListADT;
use Lambda::TermADT;
use Lambda::FreeVars;

use Lambda::LambdaModel;

plan 135;

{ # predicate free?
    is_properLambdaFn($is-free);
    
    my $x = $VarT('x');
    my $y = $VarT('y');
    my $c = $ConstT("x");   # Yes, use "x" as value!
    my $app = $AppT($x, $y);    # '(x y)'
    my $lam = $LamT($x, $app);  # 'λx.x y'

    is($is-free($x, $c), $false, "a var is never free in a ConstT");
    is($is-free($x, $x), $true, "a var is free in itself");

    is($is-free($x, $y), $false, "a var is not free in another one");
    
    is($is-free($x, $app), $true,
        "a var is free if it occurs in the function position of an application");
    is($is-free($y, $app), $true,
        "a var is free if it occurs in the argument position of an application");

    is($is-free($x, $lam), $false,
        "a var is not free in an abstraction if same as the abstraction's var");
    is($is-free($y, $lam), $true,
        "a var is free in an abstraction if different from the abstraction's var");
}


{ #predicate free-under?
    is_properLambdaFn($is-free-under);

    my $w = $VarT('w');
    my $x = $VarT('x');
    my $y = $VarT('y');
    my $z = $VarT('z');
    my $c = $ConstT("x");   # Yes, use "x" as value!
    my $a1 = $AppT($x, $y); # '(x y)'
    my $l = $LamT($x, $a1); # 'λx.x y'
    my $a2 = $AppT($l, $z); # '((λx.x y) z)'
    my $a3 = $AppT($z, $l); # '(z (λx.x y))'
    my $a4 = $AppT($l, $l); # '((λx.x y) (λx.x y))'

    my $msgNeverFree = 'free-under?: never under any binder ';
    is($is-free-under($x, $x, $c), $false, $msgNeverFree ~ 'in a ConstT');
    is($is-free-under($x, $y, $c), $false, $msgNeverFree ~ 'in a ConstT');
    is($is-free-under($x, $z, $c), $false, $msgNeverFree ~ 'in a ConstT');
                      
    is($is-free-under($x, $x, $x), $false, $msgNeverFree ~ 'in a VarT');
    is($is-free-under($x, $y, $x), $false, $msgNeverFree ~ 'in a VarT');
    is($is-free-under($x, $z, $x), $false, $msgNeverFree ~ 'in a VarT');

    # a1: (x y)
    is($is-free-under($x, $x, $a1), $false);
    is($is-free-under($x, $y, $a1), $false);
    is($is-free-under($x, $z, $a1), $false);
                        
    is($is-free-under($y, $x, $a1), $false);
    is($is-free-under($y, $y, $a1), $false);
    is($is-free-under($y, $z, $a1), $false);

    my $msgNeverIfNotOccurring = $msgNeverFree ~ 'if it doesn\'t occur at all';

    # a1: (x y)
    is($is-free-under($w, $x, $a1), $false, $msgNeverIfNotOccurring ~ ' in app of var to var');
    is($is-free-under($w, $y, $a1), $false, $msgNeverIfNotOccurring ~ ' in app of var to var');
    is($is-free-under($w, $z, $a1), $false, $msgNeverIfNotOccurring ~ ' in app of var to var');


    # a2: ((λx.x y) z)
    is($is-free-under($x, $x, $a2), $false);
    is($is-free-under($x, $y, $a2), $false);
    is($is-free-under($x, $z, $a2), $false);
                          
    is($is-free-under($y, $x, $a2), $true);
    is($is-free-under($y, $y, $a2), $false);
    is($is-free-under($y, $z, $a2), $false);
                          
    is($is-free-under($w, $x, $a2), $false, $msgNeverIfNotOccurring ~ ' in app of lambda to var');
    is($is-free-under($w, $y, $a2), $false, $msgNeverIfNotOccurring ~ ' in app of lambda to var');
    is($is-free-under($w, $z, $a2), $false, $msgNeverIfNotOccurring ~ ' in app of lambda to var');


    # a3: (z (λx.x y))
    is($is-free-under($x, $x, $a3), $false);
    is($is-free-under($x, $y, $a3), $false);
    is($is-free-under($x, $z, $a3), $false);
                          
    is($is-free-under($y, $x, $a3), $true);
    is($is-free-under($y, $y, $a3), $false);
    is($is-free-under($y, $z, $a3), $false);
                          
    is($is-free-under($w, $x, $a3), $false, $msgNeverIfNotOccurring ~ ' in app of var to lambda');
    is($is-free-under($w, $y, $a3), $false, $msgNeverIfNotOccurring ~ ' in app of var to lambda');
    is($is-free-under($w, $z, $a3), $false, $msgNeverIfNotOccurring ~ ' in app of var to lambda');


    # a4: ((λx.x y) (λx.x y))
    my $msgNotFreeIfBoundByBoth = $msgNeverFree ~ 'if bound by both, :func and :arg';
    my $msgLam2Lam = ' in app of lambda to lambda';
    is($is-free-under($x, $x, $a3), $false, $msgNotFreeIfBoundByBoth ~ $msgLam2Lam);
    is($is-free-under($x, $y, $a3), $false, $msgNotFreeIfBoundByBoth ~ $msgLam2Lam);
    is($is-free-under($x, $z, $a3), $false, $msgNotFreeIfBoundByBoth ~ $msgLam2Lam);
                          
    is($is-free-under($y, $x, $a4), $true);
    is($is-free-under($y, $y, $a4), $false);
    is($is-free-under($y, $z, $a4), $false);
                          
    is($is-free-under($w, $x, $a4), $false, $msgNeverIfNotOccurring ~ $msgLam2Lam);
    is($is-free-under($w, $y, $a4), $false, $msgNeverIfNotOccurring ~ $msgLam2Lam);
    is($is-free-under($w, $z, $a4), $false, $msgNeverIfNotOccurring ~ $msgLam2Lam);
}

{ # free-var
    is_properLambdaFn($free-var);
    
    my $x = $VarT('x');
    my $y = $VarT('y');
    my $c = $ConstT("x");   # Yes, use "x" as value!
    my $app = $AppT($x, $y);    # '(x y)'
    my $lam = $LamT($x, $app);  # 'λx.x y'

    is($free-var('x', $c),   $None,     "($free-var 'x' $c)");
    is($free-var('x', $x),   $Some($x), "($free-var 'x' $x)");

    is($free-var('x', $y),   $None,     "($free-var 'x' $y)");

    is($free-var('x', $app), $Some($x), "($free-var 'x' $app)");
    is($free-var('y', $app), $Some($y), "($free-var 'y' $app)");

    is($free-var('x', $lam), $None,     "($free-var 'x' $lam)");
    is($free-var('y', $lam), $Some($y), "($free-var 'y' $lam)");
}

{ # free-vars
    is_properLambdaFn($free-vars);
    
    my $x = $VarT('x');
    my $y = $VarT('y');
    my $c = $ConstT("x");   # Yes, use "x" as value!
    my $app1 = $AppT($x, $y);    # '(x y)'
    my $app2 = $AppT($x, $x);    # '(x x)'
    my $lam1 = $LamT($x, $app1);  # 'λx.x y'

    is($free-vars($c),   $nil,              "($free-vars $c)");
    is($free-vars($x),   $cons($x, $nil),   "($free-vars $x)");

    is($free-vars($y),   $cons($y, $nil),   "($free-vars $y)");

    my $fvs;

    $fvs = $free-vars($app1);
    $has_length($fvs, 2, "($free-vars $app1)");
    $contains_ok($x, $fvs, "(free-vars $app1)");
    $contains_ok($y, $fvs, "(free-vars $app1)");

    $fvs = $free-vars($app2);
    $has_length($fvs, 1, "($free-vars $app2) should not contain duplicates");
    $contains_ok($x, $fvs, "(free-vars $app2)");

    $fvs = $free-vars($lam1);
    $has_length($fvs, 1, "($free-vars $lam1)");
    $contains_ok($y, $fvs, "(free-vars $lam1)");
}

# -----------------------------------------------------------------------------


{ # VarT.isFree(:$in!)
    my $x = VarT.new(:name<x>);
    my $y = VarT.new(:name<y>);
    my $c = ConstT.new(:value("x"));   # Yes, use "x" as value!
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