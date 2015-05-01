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


sub diagTime(&block, Str $msg?) is export {
    if (&block.arity != 0) {
        die "expected block of arity 0 but got " ~ &block.perl;
    }
    my $time = now;
    my $out = &block();
    diag (now.Real - $time.Real).round(0.01) ~ " sec consumed" ~ ($msg.defined ?? " for $msg" !! '');
    return $out;
}

