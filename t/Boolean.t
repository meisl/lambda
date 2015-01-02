use v6;

use Test;
use Test::Util;

use Lambda::P6Currying;
use Lambda::Base;
use Lambda::Boolean;

plan 41;


# ->Str -----------------------------------------------------------------------

{ # Bool->Str
    is_properLambdaFn($Bool2Str);

    is $Bool2Str.symbol, 'Bool->Str', '$Bool2Str.symbol';
    is $Bool2Str.Str,    'Bool->Str', '$Bool2Str.Str';
}


# #true -----------------------------------------------------------------------

{ # "ctor" #true
    is_properLambdaFn($true);
    
    is $true.symbol,        '#true', '$true.symbol';
    is $true.Str,           '#true', '$true.Str';
    does_ok $true, TBool,   '#true';
    is $Bool2Str($true),    '#true', "($Bool2Str $true) -> \"#true\"";
}


# #false ----------------------------------------------------------------------

{ # "ctor" #false
    is_properLambdaFn($false);

    is $false.symbol,       '#false', '$false.symbol';
    is $false.Str,          '#false', '$false.Str';
    does_ok $false, TBool,  '#false';
    is $Bool2Str($false),   '#false', "($Bool2Str $false) -> \"#false\"";
}


# functions on Bool -----------------------------------------------------------

{ # not
    is_properLambdaFn($not);

    is $not.symbol,         'not', '$not.symbol';
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

{ # _and
    is_properLambdaFn($_and);

    is $_and($true,  $true ), $true,  '$_and($true,  $true )';
    is $_and($true,  $false), $false, '$_and($true,  $false)';
    is $_and($false, $false), $false, '$_and($false, $false)';
    is $_and($false, $true ), $false, '$_and($false, $true )';
}

{ # _or
    is_properLambdaFn($_or);

    is $_or($true,  $true ), $true,  '$_or($true,  $true )';
    is $_or($true,  $false), $true,  '$_or($true,  $false)';
    is $_or($false, $false), $false, '$_or($false, $false)';
    is $_or($false, $true ), $true,  '$_or($false, $true )';
}

{ # _if
    is_properLambdaFn($_if);

    is $_if($true, -> $_ {"x"}, -> $_ {die "alternative should not be called"}), "x", '$_if($true, -> $_ {"x"}, -> $_ {die})';
    is $_if($false, -> $_ {die "consequence should not be called"}, -> $_ {"y"}), "y", '$_if($false, -> $_ {die}, -> $_ {"x"})';

    my @seenThen = @();
    my @seenElse = @();
    my $then = curry(-> $x { @seenThen.push($x); 'then called' });
    my $else = curry(-> $x { @seenElse.push($x); 'else called' });

    is $_if($true, $then, $else), 'then called', '(_if #true ... ...) calls then-branch';
    is @seenElse.elems, 0, '(_if #true ... ...) calls then-branch (only)';

    is $_if($false, $then, $else), 'else called', '(_if #false ... ...) calls else-branch';
    is @seenThen.elems, 1, '(_if #false ... ...) calls else-branch (only)';
}
