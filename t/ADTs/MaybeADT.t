use v6;
use Test;
use Test::Util;
use Test::Util_Lambda;

use Lambda::BaseP6;
use Lambda::Boolean;


# module under test:
use Lambda::MaybeADT;


plan 60;


# ->Str -----------------------------------------------------------------------

{ # Maybe->Str
    is_properLambdaFn($Maybe2Str);

    is $Maybe2Str.symbol,   'Maybe->Str', '$Maybe2Str.symbol';
    is $Maybe2Str.Str,      'Maybe->Str', '$Maybe2Str.Str';
}


# None ------------------------------------------------------------------------

{ # ctor None
    is_properLambdaFn($None);

    is $None.symbol,        'None', '$None.symbol';
    is $None.Str,           'None', '$None.Str';
    does_ok $None, TMaybe,  'None', :msg('None is a TMaybe in itself');
    is $Maybe2Str($None),   'None', "($Maybe2Str None)";
}

{ # predicate None?
    is_properLambdaFn($is-None);

    is $is-None.symbol,         'None?', '$is-None.symbol';
    is $is-None.Str,            'None?', '$is-None.Str';
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
    is_properLambdaFn($Some);

    is $Some.symbol,            'Some', '$Some.symbol';
    is $Some.Str,               'Some', '$Some.Str';
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
    is_properLambdaFn($is-Some);

    is $is-Some.symbol,         'Some?', '$is-Some.symbol';
    is $is-Some.Str,            'Some?', '$is-Some.Str';
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
    is_properLambdaFn($Some2value);

    is $Some2value.symbol,         'Some->value', '$Some2value.symbol';
    is $Some2value.Str,            'Some->value', '$Some2value.Str';
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
