use v6;
use Test;
use Test::Util;
use Test::Util_Lambda;

use Lambda::BaseP6;
use Lambda::Boolean;


# module under test:
use Lambda::MaybeADT;

plan 15;


# TODO: findFP-inMaybe

{ # Maybe->valueWithDefault
   is_properLambdaFn($Maybe2valueWithDefault, 'Maybe->valueWithDefault');

    my $m;

    $m = $None;
    is $Maybe2valueWithDefault($m, 42), 42, "(Maybe->valueWithDefault $m 42)";

    $m = $Some(23);
    is $Maybe2valueWithDefault($m, 42), 23, "(Maybe->valueWithDefault $m 42)";
}

{ # Maybe-lift-in
   is_properLambdaFn($Maybe-lift-in, 'Maybe-lift-in');
   
    my ($f, $lifted, $v, $out);
    my @seen;

    $f = lambdaFn(
        'testFn', 'λ_.error "NYI"',
        -> $x {
            @seen.push($x);
            @seen.elems;
        }
    );

    @seen = @();
    $lifted = $Maybe-lift-in($f);
    is_validLambda($lifted);
    doesnt_ok($lifted, Definition, "lifted fn");
    is(@seen.elems, 0, "test fn should not have been called yet");

    $out = $lifted($None);
    cmp_ok($out, '===', $None, "passing None to lifted fn yields None" );
    is(@seen.elems, 0, "test fn should still not have been called");

    $v = 23;
    $out = $lifted($Some($v));
    cmp_ok($out, '===', 1, "passing a (Some {$v.perl}) to lifted fn yields whatever the test fn returns" );
    is(@seen.elems, 1,  "test fn should have been called once now");
    is(@seen[0],    $v, "test fn should have seen the (Some {$v.perl})'s value");

    $v = "forty-two";
    $out = $lifted($Some($v));
    cmp_ok($out, '===', 2, "passing a (Some {$v.perl}) to lifted fn yields whatever the test fn returns" );
    is(@seen.elems, 2,  "test fn should have been called twice now");
    is(@seen[1],    $v, "test fn should have seen the (Some {$v.perl})'s value");

}