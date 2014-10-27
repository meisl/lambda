use v6;

use Test;
use Test::Util;
use Lambda::Boolean;

use Lambda::TermADT;

plan 23;

{
    is_properLambdaFn($Term2Str);

    is_properLambdaFn($VarT);

    is_properLambdaFn($is-VarT);

    is_properLambdaFn($VarT2name);
}


{ # Term->Str
    is $Term2Str.name, 'Term->Str', '$Term2Str.name -> "Term->Str"';
    is $Term2Str.Str,  'Term->Str', '$Term2Str.Str -> "Term->Str"';
}

{ # ctor VarT
    is $VarT.name,          'VarT', '$VarT.name -> "VarT"';
    is $VarT.Str,           'VarT', '$VarT.Str -> "VarT"';
    doesnt_ok $VarT, TTerm, 'VarT', :msg('VarT is NOT a TTerm in itself');
    dies_ok { $Term2Str($VarT) }, "($Term2Str $VarT) yields error";
    
    my $x;
    $x = $VarT("foo");
    is $Term2Str($x), '(VarT "foo")',
        "($Term2Str (VarT \"foo\")) -> \"(VarT \\\"foo\\\")\"";
    does_ok $x, TTerm, "$x";
    is_validLambda $x;
}

{ # predicate VarT?
    is $is-VarT.name,          'VarT?', '$is-VarT.name -> "VarT?"';
    is $is-VarT.Str,           'VarT?', '$is-VarT.Str -> "VarT?"';
    doesnt_ok $is-VarT, TTerm, 'VarT?', :msg('VarT? is NOT a TTerm in itself');
    dies_ok {$Term2Str($is-VarT) }, "($Term2Str VarT?) yields error";

    my $x;
    $x = $VarT("foo");
    is $is-VarT($x),  $true, "($is-VarT $x) -> $true";
}

{ # projection VarT->name
    is $VarT2name.name,          'VarT->name', '$VarT2name.name -> "VarT->name"';
    is $VarT2name.Str,           'VarT->name', '$VarT2name.Str -> "VarT->name"';
    doesnt_ok $VarT2name, TTerm, 'VarT->name', :msg('VarT2name is NOT a TTerm in itself');
    dies_ok {$Term2Str($VarT2name) }, "($Term2Str VarT->name) yields error";
    
    my $x;
    $x = $VarT("foo");
    is $VarT2name($x),  'foo', "($VarT2name $x) -> \"foo\"";
}
