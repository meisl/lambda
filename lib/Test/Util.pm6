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

sub tm(&block) is export {
    if (&block.arity != 0) {
        die "expected block of arity 0 but got " ~ &block.perl;
    }
    my $time = now;
    my $out = &block();
    $time = (now.Real - $time.Real).round(0.01);
    return $out, $time;
}


sub diagTime(&block, Str $msg?) is export {
    my ($out, $time) = tm(&block);
    diag $time ~ " sec consumed" ~ ($msg.defined ?? " for $msg" !! '');
    return $out;
}

