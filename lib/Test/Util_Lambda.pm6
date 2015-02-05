use v6;

use Test;
use Test::Util;
use Lambda::BaseP6;
use Lambda::LambdaGrammar;

module Test::Util_Lambda;


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
