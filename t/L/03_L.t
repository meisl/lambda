#!nqp
use testing;
use NQPHLL;
use Util;

use L::L;


plan(3);


{
    my $c := LCompiler.new;
    

    is($c.eval('"a string"'), '"a string"', 'evaluate a string literal');
    is($c.eval('(λx.λ_.x) "bar"'), "λ_.x\n# where x = \"bar\"", 'evaluate an application');
    is($c.eval('(λx.λ_.x) "bar" "baz"'), '"bar"', 'evaluate a double application');

}

{
    my $c := nqp::getcomp('nqp');
    my $*QAST_BLOCK_NO_CLOSE := 1;

    $c.removestage('optimize');#, :before<ast>);

    #my $v := $c.compile('"a string"; sub MAIN(*@ARGS) { 23; }; return 1;', :target<ast>, :compunit_ok(1));
    my $v := $c.compile(QAST::Block.new(QAST::SVal.new(:value("a string"))), :from<ast>, :compunit_ok(0))();

    is($v, 'a string', 'evaluate a string literal');
}

done();
