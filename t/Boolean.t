use v6;

use Test;
use Test::Util;

use Lambda::Base;
use Lambda::Boolean;

plan 37;

{
    is_properLambdaFn($Bool2Str);

    is_properLambdaFn($true);
    is_properLambdaFn($false);
    
    is_properLambdaFn($not);
    is_properLambdaFn($_if);
    is_properLambdaFn($_and);
    is_properLambdaFn($_or);
}

{ # Bool->Str
    is $Bool2Str.name, 'Bool->Str', '$Bool2Str.name -> "Bool->Str"';
    is $Bool2Str.Str,  'Bool->Str', '$Bool2Str.Str -> "Bool->Str"';
}

{ # #true
    is $true.name,          '#true', '$true.name';
    is $true.Str,           '#true', '$true.Str';
    does_ok $true, TBool,   '#true';
    is $Bool2Str($true),    '#true', "($Bool2Str $true) -> \"#true\"";
}

{ # #false
    is $false.name,         '#false', '$false.name';
    is $false.Str,          '#false', '$false.Str';
    does_ok $false, TBool,  '#false';
    is $Bool2Str($false),   '#false', "($Bool2Str $false) -> \"#false\"";
}

{ # not
    is $not.name,           'not', '$not.name';
    is $not.Str,            'not', '$not.Str';
    doesnt_ok $not, TBool,  'not';
    dies_ok { $Bool2Str($not) }, "($Bool2Str $not) yields error";

    my $x;
    $x = $not($true);
    is $x, $false, "($not $true) -> $false";
    does_ok $x, TBool, "$x";
    is_validLambda $x;

    $x = $not($false);
    is $x, $true,  "($not $false) -> $true";
    does_ok $x, TBool, "$x";
    is_validLambda $x;
}

{
    is $_if($true, {"x"}, {die "alternative should not be called"}), "x", '$_if($true, {"x"}, {die})';
    is $_if($false, {die "consequence should not be called"}, {"y"}), "y", '$_if($false, {die}, {"x"})';

    is $_and($true,  $true ), $true,  '$_and($true,  $true )';
    is $_and($true,  $false), $false, '$_and($true,  $false)';
    is $_and($false, $false), $false, '$_and($false, $false)';
    is $_and($false, $true ), $false, '$_and($false, $true )';

    is $_or($true,  $true ), $true,  '$_or($true,  $true )';
    is $_or($true,  $false), $true,  '$_or($true,  $false)';
    is $_or($false, $false), $false, '$_or($false, $false)';
    is $_or($false, $true ), $true,  '$_or($false, $true )';
}
