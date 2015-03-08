use v6;

use Test;
use Test::Util;
use Test::Util_Lambda;

# module under test:
use Lambda::BaseP6;

plan 23;


{ # role lambda
    my $f;
    
    lives_ok { $f = -> $x { $x } does lambda(:lambda('foo')) }, 'can pass a Str:D as initializer';
    is $f.lambda, 'foo', '.lambda returns the initializer value';
    is $f.Str, 'foo', '.Str returns what .lambda returns';
    
    dies_ok { -> $x { $x } does lambda(:lambda(Str)) }, 'cannot pass an undefined Str as initializer';
    dies_ok { -> $x { $x } does lambda(:lambda(Callable)) }, 'cannot pass an undefined Callable as initializer';
    dies_ok { -> $x { $x } does lambda(:lambda(-> $x { $x x 10 })) }, 'cannot pass a non-0-arity Callable as initializer';

    my $callCount = 0;
    my &makeLambda = { $callCount++; 'bar' };
    $f = -> $x { $x } does lambda(:lambda(&makeLambda));
    is $callCount, 0, 'block is NOT called until .lambda has been invoked';
    is $f.Str, 'bar', '.Str returns what .lambda returns';
    is $callCount, 1, 'block is called when .lambda is invoked the first time';
    is $f.lambda, 'bar', 'can pass a block as initializer (1)';
    is $callCount, 1, 'block is NOT called again on subsequent calls to .lambda';
    is $f.lambda, 'bar', 'can pass a block as initializer (2)';
    is $callCount, 1, 'block is NOT called again on subsequent calls to .lambda';
}


{ # lambdaFn

    my $omega0 ::= lambdaFn( 'ω', 'λx.x x', -> &x { &x(&x) } );
    is_properLambdaFn($omega0);
    is $omega0.symbol, 'ω', 'ω.symbol';
    is $omega0.lambda, '(λx.x x)', 'parens are put around automatically if there aren\'t any' or die;
    
    my $callCount = 0;
    my $omega ::= lambdaFn( 'ω', { $callCount++; 'λx.x x' }, -> &x { &x(&x) } );

    is $callCount, 0, 'thunk for λ expression is not called until .lambda is called';
    is $omega.lambda, '(λx.x x)', '.lambda calls the thunk on first invocation, and auto-adds parens if needed' or die;
    is $callCount, 1, '.lambda calls the thunk ONCE on first invocation';
    is $omega.lambda, '(λx.x x)', '.lambda returns the same result on subsequent invocations';
    is $callCount, 1, '.lambda DOES NOT call the thunk again on subsequent invocations';

    is_properLambdaFn($omega);
    is $omega.symbol, 'ω', 'ω.symbol';

}


