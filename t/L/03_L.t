#!nqp
use testing;

use L::L;


plan(3);


{
    my $c := LCompiler.new;
    

    is($c.eval('"a string"'), '"a string"', 'evaluate a string literal');
    is($c.eval('(λx.λ_.x) "bar"'), 'λ_.x\n# where x = "bar"', 'evaluate an application');
    is($c.eval('(λx.λ_.x) "bar" "baz"'), '"bar"', 'evaluate a double application');

}


done();
