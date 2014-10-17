use v6;

use Test;
use Lambda::LambdaModel;

plan 26;

{
    dies_ok({ VarT.new }, 
        "VarT.new cannot be called without arg");
    dies_ok({ VarT.new("x")},
        "VarT.new cannot be called with positional Str arg");
    isa_ok(VarT.new(:name("x")), VarT,
        "VarT.new with Str arg named 'name' yields a VarT");
    dies_ok({ VarT.new(:value("x"))},
        "VarT.new MUST be called with a Str arg named 'name'");
}

{
    dies_ok({ ConstT.new }, 
        "ConstT.new cannot be called without arg");
    dies_ok({ ConstT.new("x")},
        "ConstT.new cannot be called with positional Str arg");
    isa_ok(ConstT.new(:value("x")), ConstT,
        "ConstT.new with Str arg named 'value'");
    dies_ok({ ConstT.new(:name("x")) },
        "ConstT.new MUST be called with a Str arg named 'value'")
}

{
    my $x = VarT.new(:name<x>);
    my $y = VarT.new(:name<y>);
    dies_ok({ AppT.new }, 
        "AppT.new cannot be called without arg");
    dies_ok({ AppT.new("x")},
        "AppT.new cannot be called with positional Str arg");
    isa_ok(AppT.new(:func($x), :arg($y)), AppT,
        "AppT.new with Term args named 'func' and 'arg'");
    dies_ok({ AppT.new(:func($x)) },
        "AppT.new cannot be called without Term arg named 'arg'");
    dies_ok({ AppT.new(:arg($y)) },
        "AppT.new cannot be called without Term arg named 'func'");
    dies_ok({ AppT.new(:func(Term), :arg($y)) },
        "AppT.new cannot be called with undefined Term arg named 'func'");
    dies_ok({ AppT.new(:func($x), :arg(Term)) },
        "AppT.new cannot be called with undefined Term arg named 'arg'");
    dies_ok({ AppT.new(:value($x)) },
        "AppT.new MUST be called with Term args named 'func' and 'arg'");
}

{
    my $x = VarT.new(:name<x>);
    my $y = VarT.new(:name<y>);
    my $c = ConstT.new(:value<y>);
    my $a = AppT.new(:func($x), :arg($y));
    dies_ok({ LamT.new }, 
        "LamT.new cannot be called without arg");
    dies_ok({ LamT.new("x")},
        "LamT.new cannot be called with positional Str arg");
    isa_ok(LamT.new(:var($x), :body($y)), LamT,
        "LamT.new with VarT arg named 'var' and Term arg named 'body'");
    dies_ok({ LamT.new(:var($x)) },
        "LamT.new cannot be called without arg named 'body'");
    dies_ok({ LamT.new(:body($y)) },
        "LamT.new cannot be called without arg named 'var'");
    dies_ok({ LamT.new(:var(Term), :body($y)) },
        "LamT.new cannot be called with undefined Term arg named 'var'");
    dies_ok({ LamT.new(:var($a), :body($y)) },
        "LamT.new cannot be called with an AppT arg named 'var'");
    dies_ok({ LamT.new(:var($a), :body($c)) },
        "LamT.new cannot be called with a ConstT arg named 'var'");
    dies_ok({ LamT.new(:var($x), :body(Term)) },
        "LamT.new cannot be called with undefined Term arg named 'body'");
    dies_ok({ LamT.new(:value($x)) },
        "LamT.new MUST be called with a VarT arg named 'var' and a Term arg named 'body'");
}