use v6;
use Test;
use Test::Util;

use Lambda::BaseP6;
use Lambda::Boolean;


# module under test:
use Lambda::MaybeADT;

plan 19;


# TODO: findFP-inMaybe

{ # Maybe->valueWithDefault
   is_properLambdaFn($Maybe2valueWithDefault);

    is $Maybe2valueWithDefault.symbol, 'Maybe->valueWithDefault', '$Maybe2valueWithDefault.symbol';
    is $Maybe2valueWithDefault.Str,    'Maybe->valueWithDefault', '$Maybe2valueWithDefault.Str';

    my $m;

    $m = $None;
    is $Maybe2valueWithDefault($m, 42), 42, "(Maybe->valueWithDefault $m 42)";

    $m = $Some(23);
    is $Maybe2valueWithDefault($m, 42), 23, "(Maybe->valueWithDefault $m 42)";
}

{ # Maybe-lift-in
   is_properLambdaFn($Maybe-lift-in);

    is $Maybe-lift-in.symbol, 'Maybe-lift-in', '$Maybe-lift-in.symbol';
    is $Maybe-lift-in.Str,    'Maybe-lift-in', '$Maybe-lift-in.Str';
   
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