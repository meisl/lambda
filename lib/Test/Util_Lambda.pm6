use v6;

use Test;
use Test::Util;
use Lambda::BaseP6;
use Lambda::LambdaGrammar;

module Test::Util_Lambda;


my sub fn2Str($f) {
    $f.name || $f.Str || $f.gist || $f.perl;
}

sub is_validLambda(&f) is export {
    my $fStr = fn2Str(&f);
    subtest {
        my $failed = False;
        
        does_ok(&f, lambda, 'it does role `lambda`')
            or $failed = True;
        
        my $err = Any;

        lives_ok( { try parseLambda(&f.lambda); ($err = $!) and die $! }, "its .lambda is a valid lambda-expression")
            or diag('>>>>' ~ $err) and $failed = $err;
        
        !$failed;
    }, "$fStr is valid lambda";
}

sub is_properLambdaFn(&f, Str $expectedName?) is export {
    my $fStr = fn2Str(&f);
    subtest {
        my $failed = False;
        
        my $s = &f.name;    # assuming every Callable does have a .name
        
        if $expectedName.defined {
            die 'is_properLambdaFn called with empty arg `$expectedName?`'
                if $expectedName eq '';
            is($s, $expectedName, "its .name returns {$expectedName.perl}")
                or $failed = True;
        } else {
            ok($s.defined, 'its .name returns a defined Str:D')
                or $failed = True;
            isnt($s.perl, '""', 'its .name returns a non-empty Str:D')
                or $failed = True;
            my $bt = Backtrace.new;
            $bt = $bt[$bt.last-index(*.file eq $?FILE)+1..*];
            note "WARNING: is_properLambdaFn called without \$expectedName on fn `$fStr`\n " ~ $bt;
        }

        my $orig = &f;
        dies_ok({ &f = 0 },  "it is immutable")
            or &f = $orig and $failed = True;  # reconstitute so that unrelated tests won't fail
        
        is_validLambda(&f)
            or $failed = True;

        #$failed ?? fail($failed) !! True;
        !$failed;
    }, "$fStr is proper lambdaFn";
}
