use v6;

use Test;
use Test::Util;
use Lambda::LambdaGrammar;

plan 36;

{ # single variable
    my $t;
    
    $t = parseLambda('x'); 
    does_ok($t, VarT, 'single var');
    is($t.name, 'x', 'name of single var');

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
    my $t;
    
    $t = parseLambda('x y');
    isa_ok($t, AppT, 'application of two vars');
    does_ok($t.func, VarT);
    does_ok($t.arg, VarT);

    $t = parseLambda('x y');
    isa_ok($t, AppT, 'application of two vars with parens');
    does_ok($t.func, VarT);
    does_ok($t.arg, VarT);

    $t = parseLambda('x y z');
    isa_ok($t, AppT, 'application of three vars with parens');
    isa_ok($t.func, AppT, 'application should be left-associative');
    does_ok($t.arg, VarT);
    does_ok($t.func.func, VarT);
    does_ok($t.func.arg, VarT);

    $t = parseLambda('((x y) z)');
    isa_ok($t, AppT, 'application of three vars with parens (left-assoc)');
    isa_ok($t.func, AppT);
    does_ok($t.func.func, VarT);
    does_ok($t.func.arg, VarT);

    $t = parseLambda('(x (y z))');
    isa_ok($t, AppT, 'application of three vars with parens (right-assoc)');
    does_ok($t.func, VarT);
    isa_ok($t.arg, AppT);
    does_ok($t.arg.func, VarT);
    does_ok($t.arg.arg, VarT);
}

{ # abstraction
    my $t;

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

    $t = parseLambda('λx.y');
    isa_ok($t, LamT, 'simple lambda');
    does_ok($t.var, VarT);
    does_ok($t.body, VarT);

    $t = parseLambda('λx.λy.x');
    isa_ok($t, LamT, 'two-arg lambda');
    does_ok($t.var, VarT);
    isa_ok($t.body, LamT);
    does_ok($t.body.var, VarT);
    does_ok($t.body.body, VarT);
}
