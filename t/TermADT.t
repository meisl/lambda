use v6;

use Test;
use Test::Util;
use Lambda::Boolean;

use Lambda::TermADT;

plan 54;

{
    is_properLambdaFn($Term2Str);

    is_properLambdaFn($VarT);
    is_properLambdaFn($AppT);

    is_properLambdaFn($is-VarT);
    is_properLambdaFn($is-AppT);

    is_properLambdaFn($VarT2name);
    is_properLambdaFn($AppT2func);
    is_properLambdaFn($AppT2arg);
}


# ->Str -----------------------------------------------------------------------

{ # Term->Str
    is $Term2Str.name, 'Term->Str', '$Term2Str.name';
    is $Term2Str.Str,  'Term->Str', '$Term2Str.Str';
}


# ctors -----------------------------------------------------------------------

{ # ctor VarT
    is $VarT.name,          'VarT', '$VarT.name';
    is $VarT.Str,           'VarT', '$VarT.Str';
    doesnt_ok $VarT, TTerm, 'VarT', :msg('VarT is NOT a TTerm in itself');
    dies_ok { $Term2Str($VarT) }, "($Term2Str $VarT) yields error";
    
    my $x;
    $x = $VarT("foo");
    is $Term2Str($x), '(VarT "foo")',
        "($Term2Str (VarT \"foo\")) -> \"(VarT \\\"foo\\\")\"";
    does_ok $x, TTerm, "$x";
    is_validLambda $x;
}

{ # ctor AppT
    is $AppT.name,          'AppT', '$AppT.name';
    is $AppT.Str,           'AppT', '$AppT.Str';
    doesnt_ok $AppT, TTerm, 'AppT', :msg('AppT is NOT a TTerm in itself');
    dies_ok { $Term2Str($AppT) }, "($Term2Str $AppT) yields error";
    
    my $u = $VarT('u');
    my $v = $VarT('v');
    my $x;
    $x = $AppT($u, $v);
    is $Term2Str($x), "(AppT $u $v)",
        "($Term2Str (AppT $u $v)) -> '(AppT $u $v)'";
    does_ok $x, TTerm, "$x";
    is_validLambda $x;
}


# predicates ------------------------------------------------------------------

{ # predicate VarT?
    is $is-VarT.name,          'VarT?', '$is-VarT.name';
    is $is-VarT.Str,           'VarT?', '$is-VarT.Str';
    doesnt_ok $is-VarT, TTerm, 'VarT?', :msg('VarT? is NOT a TTerm in itself');
    dies_ok {$Term2Str($is-VarT) }, "($Term2Str VarT?) yields error";

    my $x;
    $x = $VarT("foo");
    is $is-VarT($x),  $true, "($is-VarT $x)";
    
    my $u = $VarT('u');
    my $v = $VarT('v');
    $x = $AppT($u, $v);
    is $is-VarT($x),  $false, "($is-VarT $x)";
}

{ # predicate AppT?
    is $is-AppT.name,          'AppT?', '$is-AppT.name';
    is $is-AppT.Str,           'AppT?', '$is-AppT.Str';
    doesnt_ok $is-AppT, TTerm, 'AppT?', :msg('AppT? is NOT a TTerm in itself');
    dies_ok {$Term2Str($is-AppT) }, "($Term2Str AppT?) yields error";
    
    my $u = $VarT('u');
    my $v = $VarT('v');
    my $x;
    $x = $AppT($u, $v);
    is $is-AppT($x),  $true,  "($is-AppT $x)";

    is $is-AppT($u),  $false, "($is-AppT $u)";
}


# projections -----------------------------------------------------------------

{ # projection VarT->name
    is $VarT2name.name,          'VarT->name', '$VarT2name.name';
    is $VarT2name.Str,           'VarT->name', '$VarT2name.Str';
    doesnt_ok $VarT2name, TTerm, 'VarT->name', :msg('VarT2name is NOT a TTerm in itself');
    dies_ok {$Term2Str($VarT2name) }, "($Term2Str VarT->name) yields error";
    
    my $x;
    $x = $VarT("foo");
    is $VarT2name($x),  'foo', "($VarT2name $x)";

    my $u = $VarT('u');
    my $v = $VarT('v');
    $x = $AppT($u, $v);
    dies_ok( { $VarT2name($x) }, "($VarT2name $x) yields error");
}

{ # projection AppT->func
    is $AppT2func.name,          'AppT->func', '$AppT2func.name';
    is $AppT2func.Str,           'AppT->func', '$AppT2func.Str';
    doesnt_ok $AppT2func, TTerm, 'AppT->func', :msg('AppT2func is NOT a TTerm in itself');
    dies_ok {$Term2Str($AppT2func) }, "($Term2Str AppT->func) yields error";
    
    my $x;
    $x = $VarT("foo");
    dies_ok( { $AppT2func($x) }, "($AppT2func $x) yields error");

    my $u = $VarT('u');
    my $v = $VarT('v');
    $x = $AppT($u, $v);
    is $AppT2func($x), $u, "($AppT2func $x)";
}

{ # projection AppT->arg
    is $AppT2arg.name,          'AppT->arg', '$AppT2arg.name';
    is $AppT2arg.Str,           'AppT->arg', '$AppT2arg.Str';
    doesnt_ok $AppT2arg, TTerm, 'AppT->arg', :msg('AppT2arg is NOT a TTerm in itself');
    dies_ok {$Term2Str($AppT2arg) }, "($Term2Str AppT->arg) yields error";
    
    my $x;
    $x = $VarT("foo");
    dies_ok( { $AppT2arg($x) }, "($AppT2arg $x) yields error");

    my $u = $VarT('u');
    my $v = $VarT('v');
    $x = $AppT($u, $v);
    is $AppT2arg($x), $v, "($AppT2arg $x)";
}
