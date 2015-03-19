use v6;
use Test;
use Test::Util;
use Test::Util_Term;

use Lambda::Boolean;
use Lambda::TermADT;


# module under test:
use Lambda::LambdaGrammar;

plan 52;


my sub is_TermType(TTerm $term, $predicate, $msg) is hidden_from_backtrace {
    is($predicate($term), $true, $msg);
}


{ # single variable
    my $t;
    
    $t = parseLambda('x');
    is_TermType($t, $is-VarT, 'single var');
    is($VarT2name($t), 'x', 'name of single var');

    throws_like({ parseLambda('') }, X::Lambda::SyntaxError,
        :message('Syntax error: HERE>>>""'),
        'empty string',
    );

    throws_like({ parseLambda('(x)') }, X::Lambda::SyntaxError,
        :message('Syntax error: HERE>>>"(x)"'),
        'single var in parens',
    );

    throws_like({ parseLambda('   (x)') }, X::Lambda::SyntaxError,
        :message('Syntax error: "   "<<<HERE>>>"(x)"'),
        'single var in parens with leading whitespace',
    );
}

{ # string constant
    my $t;
    
    $t = parseLambda('""'); 
    is_TermType($t, $is-ConstT, 'empty Str constant');
    is($ConstT2value($t), '', 'value of Str constant');
    
    $t = parseLambda('"foo"'); 
    is_TermType($t, $is-ConstT, 'non-empty Str constant without escapes');
    is($ConstT2value($t), 'foo', 'value of Str constant non-empty Str constant without escapes');
    
    $t = parseLambda('"\\"bar\\""'); 
    is_TermType($t, $is-ConstT, 'Str constant with two escaped double quotes');
    is($ConstT2value($t), '"bar"', 'value of Str constant with two escaped double quotes');
    
    $t = parseLambda('"b\\"ar"'); 
    is_TermType($t, $is-ConstT, 'Str constant with one escaped double quote');
    is($ConstT2value($t), 'b"ar', 'value of Str constant with one escaped double quote');
    
    $t = parseLambda('"b\\"a\\\\z"'); # raw contents of this Perl6 string: "b\"a\\z"
    is_TermType($t, $is-ConstT, 'Str constant with one escaped double quote and one escaped backslash');
    is($ConstT2value($t), 'b"a\\z', 'value of Str Str constant with one escaped double quote and one escaped backslash');
    
    throws_like({ $t = parseLambda('"blah' ~ "\n" ~ 'blah"') }, X::Lambda::SyntaxError,
#        :message('Syntax error: "\"blah\nbl"<<<HERE>>>"ah\""'),    #   TODO: improve SyntaxError messages
        'string constant with newline inside',
    ) or diag("     got: {$t.Str}");
}

{ # application
    my ($t, $msg);
    
    $t = parseLambda('x y');
    $msg = 'application of two vars';
    is_TermType($t, $is-AppT, $msg);
    is_TermType($AppT2func($t), $is-VarT, "func of $msg");
    is_TermType($AppT2arg($t),  $is-VarT, "arg of $msg");
    
    $t = parseLambda('(x y)');
    $msg = 'application of two vars with parens';
    is_TermType($t, $is-AppT, $msg);
    is_TermType($AppT2func($t), $is-VarT, "func of $msg");
    is_TermType($AppT2arg($t),  $is-VarT, "arg of $msg");

    $t = parseLambda('x y z');
    $msg = 'application of three vars';
    is_TermType($t, $is-AppT, $msg);
    is_TermType($AppT2func($t), $is-AppT, "func of $msg");
    is_TermType($AppT2arg($t),  $is-VarT, "arg of $msg");
    is_TermType($AppT2func($AppT2func($t)),  $is-VarT, "func of func of $msg");
    is_TermType($AppT2arg($AppT2func($t)),   $is-VarT, "arg of func of $msg");

    $t = parseLambda('((x y) z)');
    $msg = 'application of three vars with parens (left-assoc)';
    is_TermType($t, $is-AppT, $msg);
    is_TermType($AppT2func($t), $is-AppT, "func of $msg");
    is_TermType($AppT2arg($t),  $is-VarT, "arg of $msg");
    is_TermType($AppT2func($AppT2func($t)),  $is-VarT, "func of func of $msg");
    is_TermType($AppT2arg($AppT2func($t)),   $is-VarT, "arg of func of $msg");

    $t = parseLambda('(x (y z))');
    $msg = 'application of three vars with parens (right-assoc)';
    is_TermType($t, $is-AppT, $msg);
    is_TermType($AppT2func($t), $is-VarT, "func of $msg");
    is_TermType($AppT2arg($t),  $is-AppT, "arg of $msg");
    is_TermType($AppT2func($AppT2arg($t)),  $is-VarT, "func of arg of $msg");
    is_TermType($AppT2arg($AppT2arg($t)),   $is-VarT, "arg of arg of $msg");

    $t = parseLambda('(λx.x)(λx.x)');
    $msg = '(λx.x)(λx.x) - no space in between';
    is_TermType($t, $is-AppT, $msg);
    my $func = $AppT2func($t);
    my $arg  = $AppT2arg($t);
    is_TermType($func, $is-LamT, "func of $msg");
    is_TermType($arg,  $is-LamT, "arg of $msg");
    is_eq($func, $arg);
}

{ # abstraction
    my ($act, $exp, $msg);

    throws_like({ parseLambda('λ') }, X::Lambda::SyntaxError,
        :message('Syntax error: HERE>>>"λ"'),
        'single lambda',
    );

    throws_like({ parseLambda('λ.x') }, X::Lambda::SyntaxError,
        :message('Syntax error: HERE>>>"λ.x"'),
        'lambda without var',
    );

    throws_like({ parseLambda('λx.') }, X::Lambda::SyntaxError,
        :message('Syntax error: HERE>>>"λx."'),
        'lambda without body',
    );

    $act = parseLambda('λx.y');
    $msg = 'simple lambda';
    is_TermType($act, $is-LamT, $msg);
    isa_ok($LamT2var($act), Str, "var of $msg");    # DONE: LamT_ctor_with_Str_binder
    is_TermType($LamT2body($act), $is-VarT, "body of $msg");

    $act = parseLambda('λx.λy.x');
    $msg = 'two-arg lambda';
    is_TermType($act, $is-LamT, $msg);
    isa_ok($LamT2var($act), Str, "var of $msg");    # DONE: LamT_ctor_with_Str_binder
    is_TermType($LamT2body($act), $is-LamT, "body of $msg");
    isa_ok($LamT2var($LamT2body($act)), Str, "var of body of $msg");    # DONE: LamT_ctor_with_Str_binder
    is_TermType($LamT2body($LamT2body($act)), $is-VarT, "body of body of $msg");
}
