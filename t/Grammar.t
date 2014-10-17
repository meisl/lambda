use v6;

use Test;
use Lambda::LambdaGrammar;

plan 36;

{ # single variable
    my $t;
    
    $t = λ('x'); 
    isa_ok($t, VarT, 'single var');
    is($t.name, 'x', 'name of single var');

    throws_like({ λ('') }, X::Lambda::SyntaxError,
        :message('Syntax error: HERE>>>""'),
        'empty string',
    );

    throws_like({ λ('(x)') }, X::Lambda::SyntaxError,
        :message('Syntax error: HERE>>>"(x)"'),
        'single var in parens',
    );

    throws_like({ λ('   (x)') }, X::Lambda::SyntaxError,
        :message('Syntax error: "   "<<<HERE>>>"(x)"'),
        'single var in parens with leading whitespace',
    );
}

{ # application
    my $t;
    
    $t = λ('x y');
    isa_ok($t, AppT, 'application of two vars');
    isa_ok($t.func, VarT);
    isa_ok($t.arg, VarT);

    $t = λ('x y');
    isa_ok($t, AppT, 'application of two vars with parens');
    isa_ok($t.func, VarT);
    isa_ok($t.arg, VarT);

    $t = λ('x y z');
    isa_ok($t, AppT, 'application of three vars with parens');
    isa_ok($t.func, AppT, 'application should be left-associative');
    isa_ok($t.arg, VarT);
    isa_ok($t.func.func, VarT);
    isa_ok($t.func.arg, VarT);

    $t = λ('((x y) z)');
    isa_ok($t, AppT, 'application of three vars with parens (left-assoc)');
    isa_ok($t.func, AppT);
    isa_ok($t.func.func, VarT);
    isa_ok($t.func.arg, VarT);

    $t = λ('(x (y z))');
    isa_ok($t, AppT, 'application of three vars with parens (right-assoc)');
    isa_ok($t.func, VarT);
    isa_ok($t.arg, AppT);
    isa_ok($t.arg.func, VarT);
    isa_ok($t.arg.arg, VarT);
}

{ # abstraction
    my $t;

    throws_like({ λ('λ') }, X::Lambda::SyntaxError,
        :message('Syntax error: HERE>>>"λ"'),
        'single lambda',
    );

    throws_like({ λ('λ.x') }, X::Lambda::SyntaxError,
        :message('Syntax error: HERE>>>"λ.x"'),
        'lambda without var',
    );

    throws_like({ λ('λx.') }, X::Lambda::SyntaxError,
        :message('Syntax error: HERE>>>"λx."'),
        'lambda without body',
    );

    $t = λ('λx.y');
    isa_ok($t, LamT, 'simple lambda');
    isa_ok($t.var, VarT);
    isa_ok($t.body, VarT);

    $t = λ('λx.λy.x');
    isa_ok($t, LamT, 'two-arg lambda');
    isa_ok($t.var, VarT);
    isa_ok($t.body, LamT);
    isa_ok($t.body.var, VarT);
    isa_ok($t.body.body, VarT);
}
