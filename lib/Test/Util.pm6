use v6;

use Test;

module Test::Util;


sub does_ok($actual, $expectedRole, Str $name?, Str :$msg) is export {
    ok($actual ~~ $expectedRole, 
        ($name // 'it') ~ " should do {$expectedRole.^name}" ~ ($msg.defined ?? " - $msg" !! '')
    ) or diag("  Expected role: {$expectedRole.^name}\n  Actual type: " ~ $actual.^name) and False;
}

sub doesnt_ok($actual, $expectedRole, Str $name?, Str :$msg) is export {
    ok($actual !~~ $expectedRole, 
        ($name // 'it') ~ " should NOT do {$expectedRole.^name}" ~ ($msg.defined ?? " - $msg" !! '')
    ) or diag("  Expected NOT: {$expectedRole.^name}\n  Actual type: " ~ $actual.^name) and False;
}
