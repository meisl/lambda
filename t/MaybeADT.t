use v6;

use Test;
use Test::Util;
use Lambda::Boolean;

use Lambda::MaybeADT;

plan 56;

{
    is_properLambdaFn($Maybe2Str);

    is_properLambdaFn($None);
    is_properLambdaFn($Some);

    is_properLambdaFn($is-None);
    is_properLambdaFn($is-Some);

    is_properLambdaFn($Some2value);
}


{ # Maybe->Str
    is $Maybe2Str.name, 'Maybe->Str', '$Maybe2Str.name -> "Maybe->Str"';
    is $Maybe2Str.Str,  'Maybe->Str', '$Maybe2Str.Str -> "Maybe->Str"';
}

{ # ctor None
    is $None.name,          'None', '$None.name -> "None"';
    is $None.Str,           'None', '$None.Str -> "None"';
    does_ok $None, TMaybe,  'None', :msg('None is a TMaybe in itself');
    is $Maybe2Str($None),   'None', "($Maybe2Str None) -> \"None\"";
}

{ # ctor Some
    is $Some.name,              'Some', '$Some.name -> "Some"';
    is $Some.Str,               'Some', '$Some.Str -> "Some"';
    doesnt_ok $Some, TMaybe,    'Some', :msg('Some is NOT a TMaybe in itself');
    dies_ok { $Maybe2Str($Some) }, "($Maybe2Str $Some) yields error";
    
    my $x;
    $x = $Some(42);
    is $Maybe2Str($x), '(Some 42)',
        "($Maybe2Str (Some 42)) -> \"(Some 42)\"";
    does_ok $x, TMaybe, "$x";
    is_validLambda $x;

    $x = $Some("foo");
    is $Maybe2Str($x), '(Some "foo")',
        "($Maybe2Str (Some \"foo\")) -> \"(Some \\\"foo\\\")\"";
    does_ok $x, TMaybe, "$x";
    is_validLambda $x;

    # can "stack 'em":

    $x = $Some($None);
    is $Maybe2Str($x), '(Some None)',
        "($Maybe2Str (Some None)) -> \"(Some None)\"";
    does_ok $x, TMaybe, "$x";
    is_validLambda $x;

    $x = $Some($Some(23));
    is $Maybe2Str($x), '(Some (Some 23))',
        "($Maybe2Str (Some (Some 23))) -> \"(Some (Some 23))\"";
    does_ok $x, TMaybe, "$x";
    is_validLambda $x;
}

{ # predicate None?
    is $is-None.name,           'None?', '$is-None.name -> "None?"';
    is $is-None.Str,            'None?', '$is-None.Str -> "None?"';
    doesnt_ok $is-None, TMaybe, 'None?', :msg('None? is NOT a TMaybe in itself');
    dies_ok {$Maybe2Str($is-None) }, "($Maybe2Str None?) yields error";
    
    my $x;
    $x = $None;
    is $is-None($x), $true,  "($is-None $x) -> $true";

    $x = $Some(5);
    is $is-None($x),  $false, "($is-None $x) -> $false";

    $x = $Some("foo");
    is $is-None($x),  $false, "($is-None $x) -> $false";

    $x = $Some($None);
    is $is-None($x),  $false, "($is-None $x) -> $false";

    $x = $Some($Some("foo"));
    is $is-None($x),  $false, "($is-None $x) -> $false";
}

{ # predicate Some?
    is $is-Some.name,           'Some?', '$is-Some.name -> "Some?"';
    is $is-Some.Str,            'Some?', '$is-Some.Str -> "Some?"';
    doesnt_ok $is-Some, TMaybe, 'Some?', :msg('Some? is NOT a TMaybe in itself');
    dies_ok {$Maybe2Str($is-Some) }, "($Maybe2Str Some?) yields error";
    
    my $x;
    $x = $None;
    is $is-Some($x), $false,  "($is-Some $x) -> $false";

    $x = $Some(5);
    is $is-Some($x),  $true, "($is-Some $x) -> $true";

    $x = $Some("foo");
    is $is-Some($x),  $true, "($is-Some $x) -> $true";

    $x = $Some($None);
    is $is-Some($x),  $true, "($is-Some $x) -> $true";

    $x = $Some($Some("foo"));
    is $is-Some($x),  $true, "($is-Some $x) -> $true";
}

{ # projection Some->value
    is $Some2value.name,           'Some->value', '$Some2value.name -> "Some->value"';
    is $Some2value.Str,            'Some->value', '$Some2value.Str -> "Some->value"';
    doesnt_ok $Some2value, TMaybe, 'Some->value', :msg('Some2value is NOT a TMaybe in itself');
    dies_ok {$Maybe2Str($Some2value) }, "($Maybe2Str Some->value) yields error";
    
    
    my $x;
    $x = $None;
    dies_ok { $Some2value($x) },  "($Some2value $x) yields error";

    $x = $Some(5);
    is $Some2value($x),  5, "($Some2value $x) -> 5";

    $x = $Some("foo");
    is $Some2value($x),  'foo', "($Some2value $x) -> \"foo\"";

    $x = $Some($None);
    is $Some2value($x),  $None, "($Some2value $x) -> $None";

    $x = $Some($Some("foo"));
    is $Some2value($x),  $Some("foo"), "($Some2value $x) -> ($Some \"foo\")";

    is $Some2value($Some2value($x)),  'foo', "($Some2value ($Some2value $x)) -> \"foo\"";
}
