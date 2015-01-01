use v6;

use Test;
use Lambda::Base;
use Lambda::LambdaGrammar;

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

sub is_validLambda($f) is export {
    my $fStr = $f.?symbol || $f.Str || $f.gist || $f.perl;
    subtest {
        my $failed = False;

        does_ok($f, lambda, "$f")
            or $failed = True;
        
        does_ok($f, Callable, "$f")
            or $failed = True;
        
        my $err = Any;

        lives_ok( { try parseLambda($f.lambda); ($err = $!) and die $! }, "$fStr.lambda should be valid lambda-expression")
            or diag('>>>>' ~ $err) and $failed = $err;
        
        !$failed;
    }, "$fStr is valid lambda";
}

sub is_properLambdaFn($f is rw) is export {
    subtest {
        my $failed = False;

        does_ok($f, Definition, "$f")
            or $failed = True;
        
        my $orig = $f;
        dies_ok({ $f = 0 },  "$orig is immutable")
            or $f = $orig and $failed = True;  # reconstitute so that unrelated tests won't fail
        
        is_validLambda($f)
            or $failed = True;

        #$failed ?? fail($failed) !! True;
        !$failed;
    }, ($f.Str || $f.gist || $f.perl) ~ ' is proper lambdaFn';
}
