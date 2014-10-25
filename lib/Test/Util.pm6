use v6;

use Test;
use Lambda::Base;

module Test::Util;


sub does_ok($actual, $expectedRole, Str $msg?) is export {
    ok($actual ~~ $expectedRole, ($msg // 'it') ~ " does {$expectedRole.^name}")
        || diag "  Expected role: {$expectedRole.^name}\n  Actual type: " ~ $actual.^name;
}

sub is_properLambdaFn($f is rw) is export {
    dies_ok { $f      = 0 },  "\$$f is immutable";
    does_ok   $f,     lambda, "\$$f";
    does_ok   $f,     name,   "\$$f";
}

