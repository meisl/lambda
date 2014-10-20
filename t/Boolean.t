use v6;

use Test;
use Lambda::Boolean;

plan 22;

{
    dies_ok({ $true     = 0 }, '$true is immutable');
    dies_ok({ $false    = 0 }, '$false is immutable');
    dies_ok({ $bool2str = 0 }, '$bool2str is immutable');
    dies_ok({ $not      = 0 }, '$not is immutable');
    dies_ok({ $_if      = 0 }, '$_if is immutable');
    dies_ok({ $_and     = 0 }, '$_and is immutable');
    dies_ok({ $_or      = 0 }, '$_or is immutable');
}

{
    is $bool2str($true), "#true", '$bool2str($true)';
    is $bool2str($false), "#false", '$bool2str($false)';

    is $true.Str,  '#true',  '$true.Str';
    is $false.Str, '#false', '$false.Str';

    is $not($true), $false, '$not(true)';

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
