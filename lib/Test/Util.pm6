use v6;

use Test;

module Test::Util;

sub does_ok($actual, $expectedRole, Str $msg?) is export {
    ok($actual ~~ $expectedRole, ($msg // 'it') ~ " does {$expectedRole.^name}")
        || diag "  Expected role: {$expectedRole.^name}\n  Actual type: " ~ $actual.^name;
}
