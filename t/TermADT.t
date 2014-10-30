use v6;

use Test;
use Test::Util;
use Lambda::Base;
use Lambda::Boolean;

use Lambda::TermADT;

plan 95;


# ->Str -----------------------------------------------------------------------

{ # Term->Str
    is_properLambdaFn($Term2Str);

    is $Term2Str.symbol, 'Term->Str', '$Term2Str.symbol';
    is $Term2Str.Str,    'Term->Str', '$Term2Str.Str';
}


# VarT ------------------------------------------------------------------------

{ # ctor VarT
    is_properLambdaFn($VarT);

    is $VarT.symbol,        'VarT', '$VarT.symbol';
    is $VarT.Str,           'VarT', '$VarT.Str';
    doesnt_ok $VarT, TTerm, 'VarT', :msg('VarT is NOT a TTerm in itself');
    dies_ok { $Term2Str($VarT) }, "($Term2Str $VarT) yields error";
    
    my $x;
    $x = $VarT("foo");
    is $Term2Str($x), '(VarT "foo")',
        "($Term2Str (VarT \"foo\"))";
    does_ok $x, TTerm, "$x";
    is_validLambda $x;
    doesnt_ok $x, Definition;
}

{ # predicate VarT?
    is_properLambdaFn($is-VarT);

    is $is-VarT.symbol,        'VarT?', '$is-VarT.symbol';
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
    
    $x = $LamT($u, $v);
    is $is-VarT($x),  $false, "($is-VarT $x)";
}

{ # projection VarT->name
    is_properLambdaFn($VarT2name);

    is $VarT2name.symbol,        'VarT->name', '$VarT2name.symbol';
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

    $x = $LamT($u, $v);
    dies_ok( { $VarT2name($x) }, "($VarT2name $x) yields error");
}


# AppT ------------------------------------------------------------------------

{ # ctor AppT
    is_properLambdaFn($AppT);

    is $AppT.symbol,        'AppT', '$AppT.symbol';
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
    doesnt_ok $x, Definition;
}

{ # predicate AppT?
    is_properLambdaFn($is-AppT);

    is $is-AppT.symbol,        'AppT?', '$is-AppT.symbol';
    is $is-AppT.Str,           'AppT?', '$is-AppT.Str';
    doesnt_ok $is-AppT, TTerm, 'AppT?', :msg('AppT? is NOT a TTerm in itself');
    dies_ok {$Term2Str($is-AppT) }, "($Term2Str AppT?) yields error";
    
    my $u = $VarT('u');
    my $v = $VarT('v');

    is $is-AppT($u),  $false, "($is-AppT $u)";

    my $x;
    $x = $AppT($u, $v);
    is $is-AppT($x),  $true,  "($is-AppT $x)";
    
    $x = $LamT($u, $v);
    is $is-AppT($x),  $false, "($is-AppT $x)";
}

{ # projection AppT->func
    is_properLambdaFn($AppT2func);

    is $AppT2func.symbol,        'AppT->func', '$AppT2func.symbol';
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

    $x = $LamT($u, $v);
    dies_ok( { $AppT2func($x) }, "($AppT2func $x) yields error");
}

{ # projection AppT->arg
    is_properLambdaFn($AppT2arg);

    is $AppT2arg.symbol,        'AppT->arg', '$AppT2arg.symbol';
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

    $x = $LamT($u, $v);
    dies_ok( { $AppT2arg($x) }, "($AppT2arg $x) yields error");
}


# LamT ------------------------------------------------------------------------

{ # ctor LamT
    is_properLambdaFn($LamT);

    is $LamT.symbol,        'LamT', '$LamT.symbol';
    is $LamT.Str,           'LamT', '$LamT.Str';
    doesnt_ok $LamT, TTerm, 'LamT', :msg('LamT is NOT a TTerm in itself');
    dies_ok { $Term2Str($LamT) }, "($Term2Str $LamT) yields error";
    
    my $u = $VarT('u');
    my $v = $VarT('v');
    my $x;
    $x = $LamT($u, $v);
    is $Term2Str($x), "(LamT $u $v)",
        "($Term2Str (LamT $u $v)) -> '(LamT $u $v)'";
    does_ok $x, TTerm, "$x";
    is_validLambda $x;
    doesnt_ok $x, Definition;

    dies_ok({ $LamT($x, $v) }, "($LamT $x $v) yields an error");
}

{ # predicate LamT?
    is_properLambdaFn($is-LamT);

    is $is-LamT.symbol,        'LamT?', '$is-LamT.symbol';
    is $is-LamT.Str,           'LamT?', '$is-LamT.Str';
    doesnt_ok $is-LamT, TTerm, 'LamT?', :msg('LamT? is NOT a TTerm in itself');
    dies_ok {$Term2Str($is-LamT) }, "($Term2Str LamT?) yields error";
    
    my $u = $VarT('u');
    my $v = $VarT('v');
    my $x;
    $x = $LamT($u, $v);
    is $is-LamT($x),  $true,  "($is-LamT $x)";
    
    $x = $AppT($u, $v);
    is $is-LamT($x),  $false, "($is-LamT $x)";

    is $is-LamT($u),  $false, "($is-LamT $u)";
}

{ # projection LamT->var
    is_properLambdaFn($LamT2var);

    is $LamT2var.symbol,        'LamT->var', '$LamT2var.symbol';
    is $LamT2var.Str,           'LamT->var', '$LamT2var.Str';
    doesnt_ok $LamT2var, TTerm, 'LamT->var', :msg('LamT2var is NOT a TTerm in itself');
    dies_ok {$Term2Str($LamT2var) }, "($Term2Str LamT->var) yields error";
    
    my $x;
    $x = $VarT("foo");
    dies_ok( { $LamT2var($x) }, "($LamT2var $x) yields error");

    my $u = $VarT('u');
    my $v = $VarT('v');
    $x = $AppT($u, $v);
    dies_ok( { $LamT2var($x) }, "($LamT2var $x) yields error");

    $x = $LamT($u, $v);
    is $LamT2var($x), $u, "($LamT2var $x)";
}

{ # projection LamT->body
    is_properLambdaFn($LamT2body);

    is $LamT2body.symbol,        'LamT->body', '$LamT2body.symbol';
    is $LamT2body.Str,           'LamT->body', '$LamT2body.Str';
    doesnt_ok $LamT2body, TTerm, 'LamT->body', :msg('LamT2body is NOT a TTerm in itself');
    dies_ok {$Term2Str($LamT2body) }, "($Term2Str LamT->body) yields error";
    
    my $x;
    $x = $VarT("foo");
    dies_ok( { $LamT2body($x) }, "($LamT2body $x) yields error");

    my $u = $VarT('u');
    my $v = $VarT('v');
    $x = $AppT($u, $v);
    dies_ok( { $LamT2body($x) }, "($LamT2body $x) yields error");

    $x = $LamT($u, $v);
    is $LamT2body($x), $v, "($LamT2body $x)";
}
