#!nqp
use QAST;   # that is, nqp'S

use testing;
use Util::QAST;

plan(19);


my $s := QAST::SVal.new(:value<bar>);
is(dump($s), '─◙ SVal "bar"', 'dump str constant');

my $i := QAST::IVal.new(:value(23));
is(dump($i), '─◙ IVal 23', 'dump int constant');

my $n := QAST::NVal.new(:value(3.1415));
is(dump($n), '─◙ NVal 3.1415', 'dump num constant');
is(dump(QAST::NVal.new(:value(nqp::inf))), '─◙ NVal Inf', 'dump num constant with value inf');


my $b := QAST::Block.new();
is(dump($b), '──:Block', 'dump Block');
is(dump($b, :indent('    ')), '    ──:Block', 'dump Block with indent');
is(dump($b, :oneLine), '(Block)', 'dump Block on one line');

my $nullop := QAST::Op.new(:op<null>);
is(dump($nullop), '──null', 'dump Op null');
is(dump($nullop, :indent('    ')), '    ──null', 'dump Op null with indent');
is(dump($nullop, :oneLine), '(null)', 'dump Op null on one line');

$b.push($nullop);
is(dump($b), "──:Block\n  ╙─null", 'dump Block with child Op null');
is(dump($b, :indent('# ')), "# ──:Block\n#   ╙─null", 'dump Block with child Op null with indent');
is(dump($b, :oneLine), "((Block) (null))", 'dump Block with child Op null on one line');


my $v := QAST::Var.new(:name<foo>);
is(dump($v), '─○  foo :decl()', 'dump Var w/out explicit scope');
$v.decl(nqp::null_s);   # bug in QAST::Var
is(dump($v), '─○  foo', 'dump Var w/out explicit scope and :decl set to null_s');

$v.scope('lexical');
is(dump($v), '─○ lexical foo', 'dump Var with explicit scope');

$b.push($v);
is(dump($b), "──:Block\n  ╟─null\n  ╙○ lexical foo", 'dump Block with children');
is(dump($b, :indent('# ')), "# ──:Block\n#   ╟─null\n#   ╙○ lexical foo", 'dump Block with children with indent');
is(dump($b, :oneLine), "((Block) (null) ( lexical foo))", 'dump Block with children on one line');

