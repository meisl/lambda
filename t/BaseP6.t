use v6;

use Test;
use Test::Util;

# module under test:
use Lambda::BaseP6;

plan 2;


{ # lambdaFn
    my $omega ::= lambdaFn( 'ω', 'λx.x x', -> &x { &x(&x) } );
   is_properLambdaFn($omega);

   is $omega.symbol, 'ω', 'ω.symbol';
}
