use v6;

use Test;
use Lambda::Base;
use Lambda::LambdaGrammar;

module Test::Util;


sub does_ok($actual, $expectedRole, Str $msg?) is export {
    ok($actual ~~ $expectedRole, ($msg // 'it') ~ " does {$expectedRole.^name}")
        || diag "  Expected role: {$expectedRole.^name}\n  Actual type: " ~ $actual.^name;
}

sub is_properLambdaFn($f is rw) is export {
    my $failed = False;
    does_ok($f,     name,   "$f")
        or $failed = True;
    does_ok($f,     lambda, "$f")
        or $failed = True;
    
    my $orig = $f;
    dies_ok({ $f = 0 },  "$orig is immutable")
        or $f = $orig and $failed = True;  # reconstitute so that unrelated tests won't fail
    
    my $err = Any;
    lives_ok( { try λ($f.lambda); ($err = $!) and die $! }, "{$f.name}.lambda should be valid lambda-expression")
        or diag('>>>>' ~ $err) and $failed = $err;
    
    #$failed ?? fail($failed) !! True;
    return !$failed;
}

