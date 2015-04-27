use v6;
use Test;
use Test::Util;
use Test::Util_Lambda;

use Lambda::BaseP6;
use Lambda::Boolean;


# module under test:
use Lambda::MaybeADT;


plan 66;


# ->Str -----------------------------------------------------------------------

{ # Maybe->Str
    is_properLambdaFn($Maybe2Str, 'Maybe->Str');
}


# None ------------------------------------------------------------------------

{ # ctor None
    is_properLambdaFn($None, 'None');

    does_ok $None, TMaybe,  'None', :msg('None is a TMaybe in itself');
    is $Maybe2Str($None),   'None', "($Maybe2Str None)";
}

{ # predicate None?
    is_properLambdaFn($is-None, 'None?');

    doesnt_ok $is-None, TMaybe, 'None?', :msg('None? is NOT a TMaybe in itself');
    dies_ok {$Maybe2Str($is-None) }, "($Maybe2Str None?) yields error";
    
    my $x;
    $x = $None;
    is $is-None($x), $true,  "($is-None $x)";

    $x = $Some(5);
    is $is-None($x),  $false, "($is-None $x)";

    $x = $Some("foo");
    is $is-None($x),  $false, "($is-None $x)";

    $x = $Some($None);
    is $is-None($x),  $false, "($is-None $x)";

    $x = $Some($Some("foo"));
    is $is-None($x),  $false, "($is-None $x)";
}


# Some ------------------------------------------------------------------------

{ # ctor Some
    is_properLambdaFn($Some, 'Some');

    doesnt_ok $Some, TMaybe,    'Some', :msg('Some is NOT a TMaybe in itself');
    dies_ok { $Maybe2Str($Some) }, "($Maybe2Str $Some) yields error";
    
    my $x;
    $x = $Some(42);
    is $Maybe2Str($x), '(Some 42)',
        "($Maybe2Str (Some 42))";
    does_ok $x, TMaybe, "$x";
    doesnt_ok $x, Definition, "$x";
    is_validLambda $x;

    $x = $Some("foo");
    is $Maybe2Str($x), '(Some "foo")',
        "($Maybe2Str (Some \"foo\"))";
    does_ok $x, TMaybe, "$x";
    doesnt_ok $x, Definition, "$x";
    is_validLambda $x;

    # can "stack 'em":

    $x = $Some($None);
    is $Maybe2Str($x), '(Some None)',
        "($Maybe2Str (Some None))";
    does_ok $x, TMaybe, "$x";
    doesnt_ok $x, Definition, "$x";
    is_validLambda $x;

    $x = $Some($Some(23));
    is $Maybe2Str($x), '(Some (Some 23))',
        "($Maybe2Str (Some (Some 23)))";
    does_ok $x, TMaybe, "$x";
    doesnt_ok $x, Definition, "$x";
    is_validLambda $x;
}


{ # predicate Some?
    is_properLambdaFn($is-Some, 'Some?');

    doesnt_ok $is-Some, TMaybe, 'Some?', :msg('Some? is NOT a TMaybe in itself');
    dies_ok {$Maybe2Str($is-Some) }, "($Maybe2Str Some?) yields error";
    
    my $x;
    $x = $None;
    is $is-Some($x), $false,  "($is-Some $x)";

    $x = $Some(5);
    is $is-Some($x),  $true, "($is-Some $x)";

    $x = $Some("foo");
    is $is-Some($x),  $true, "($is-Some $x)";

    $x = $Some($None);
    is $is-Some($x),  $true, "($is-Some $x)";

    $x = $Some($Some("foo"));
    is $is-Some($x),  $true, "($is-Some $x)";
}

{ # projection Some->value
    is_properLambdaFn($Some2value, 'Some->value');

    doesnt_ok $Some2value, TMaybe, 'Some->value', :msg('Some2value is NOT a TMaybe in itself');
    dies_ok {$Maybe2Str($Some2value) }, "($Maybe2Str Some->value) yields error";
    
    
    my $x;
    $x = $None;
    dies_ok { $Some2value($x) },  "($Some2value $x) yields error";

    $x = $Some(5);
    is $Some2value($x),  5, "($Some2value $x)";

    $x = $Some("foo");
    is $Some2value($x),  'foo', "($Some2value $x)";

    $x = $Some($None);
    is $Some2value($x),  $None, "($Some2value $x)";

    $x = $Some($Some("foo"));
    is $Some2value($x),  $Some("foo"), "($Some2value $x)";

    is $Some2value($Some2value($x)),  'foo', "($Some2value ($Some2value $x))";
}


# functions on Maybe ----------------------------------------------------------

{ # ->findFP-inMaybe ----------------------------------------------------------
    my $f = lambdaFn(
        Str, 'λn.if (lte? n 0) None (Some (- n 1))',
        -> Int $n { $n <= 0 ?? $None !! $Some($n-1) }
    );
    
    is $findFP-inMaybe($f, 0), $None,    "findFP-inMaybe $f 0";
    is $findFP-inMaybe($f, 1), $Some(0), "findFP-inMaybe $f 1";
    is $findFP-inMaybe($f, 5), $Some(0), "findFP-inMaybe $f 5";
}

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
