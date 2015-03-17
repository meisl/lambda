use v6;
use Test;
use Test::Util;

use Lambda::Boolean;
use Lambda::TermADT;


# module under test:
use Lambda::LambdaGrammar;

plan 37;


my sub is_TermType(TTerm $term, $predicate, $msg) {
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
