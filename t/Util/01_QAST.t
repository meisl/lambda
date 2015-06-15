#!nqp
use QAST;   # that is, nqp'S

use testing;
use Util;

use Util::QAST;

plan(42);


my $s := QAST::SVal.new(:value<bar>);
is(dump($s), '─◙ SVal "bar"', 'dump str constant');

my $i := QAST::IVal.new(:value(23));
is(dump($i), '─◙ IVal 23', 'dump int constant');

my $n := QAST::NVal.new(:value(3.1415));
is(dump($n), '─◙ NVal 3.1415', 'dump num constant');
is(dump(QAST::NVal.new(:value(nqp::inf))), '─◙ NVal Inf', 'dump num constant with value inf');

my $nullop := QAST::Op.new(:op<null>);
is(dump($nullop), '──null', 'dump Op null');
is(dump($nullop, :indent('    ')), '    ──null', 'dump Op null with indent');
is(dump($nullop, :oneLine), '(null)', 'dump Op null on one line');


my $v := QAST::Var.new(:name<foo>);
is(dump($v), '─○  foo :decl()', 'dump Var w/out explicit scope');
$v.decl(nqp::null_s);   # bug in QAST::Var
is(dump($v), '─○  foo', 'dump Var w/out explicit scope and :decl set to null_s');

$v.scope('lexical');
is(dump($v), '─○ lexical foo', 'dump Var with explicit scope');


my $stmts := QAST::Stmts.new($nullop, $v);
is(dump($stmts),
             "──:Stmts"
         ~ "\n  ├─null"
         ~ "\n  └○ lexical foo", 
    'dump Stmts with children uses single vertical line to connect children');
dies_ok( { ~$stmts }, 'stringifying QAST::Stmts as is');
$stmts.HOW.mixin($stmts, StrByDump);
is(~$stmts, 
             "──:Stmts+\{StrByDump}"
         ~ "\n  ├─null"
         ~ "\n  └○ lexical foo", 
    'with role StrByDump mixed in it uses dump to stringify');

my $b := QAST::Block.new();
is(dump($b), '──:Block', 'dump Block');
is(dump($b, :indent('    ')), '    ──:Block', 'dump Block with indent');
is(dump($b, :oneLine), '(Block)', 'dump Block on one line');

$b.push($nullop);
is(dump($b), "──:Block\n  ╙─null", 'dump Block with child uses double vertical line to connect child');
is(dump($b, :indent('# ')), "# ──:Block\n#   ╙─null", 'dump Block with child with indent');
is(dump($b, :oneLine), "((Block) (null))", 'dump Block with child on one line');

$b.push($v);
is(dump($b), 
             "──:Block"
         ~ "\n  ╟─null"
         ~ "\n  ╙○ lexical foo", 
    'dump Block with children uses double vertical line to connect children');
is(dump($b, :indent('# ')), 
            "# ──:Block"
        ~ "\n#   ╟─null"
        ~ "\n#   ╙○ lexical foo", 
    'dump Block with children with indent uses double vertical line to connect children');
is(dump($b, :oneLine), "((Block) (null) ( lexical foo))", 'dump Block with children on one line');



# role StrByDump
dies_ok( { ~$b }, 'stringifying QAST::Block as is');
$b.HOW.mixin($b, StrByDump);
is(~$b,  
           "──:Block+\{StrByDump}"
         ~ "\n  ╟─null"
         ~ "\n  ╙○ lexical foo", 
    'with role StrByDump mixed in it uses dump to stringify')
    || diag("\n$b");


# removeChild

my $barVar := QAST::Var.new(:name<bar>);
my $block := QAST::Block.new(
    QAST::Var.new(:name<qumbl>),
    $barVar,
    QAST::Var.new(:name<foo>),
);
is(nqp::elems($block.list), 3, 'nr of children before removing one');
dies_ok( { removeChild($block, QAST::Var.new(:name<baz>)) }, 'removing non-existent child');
dies_ok( { removeChild($block, QAST::Var.new(:name<bar>)) }, 'removing non-existent child (even if looks like one)');
lives_ok( { removeChild($block, $barVar) }, 'removing existent child');
is(nqp::elems($block.list), 2, 'nr of children after removing one');
is($block[0].name, 'qumbl', 'preceding sibling untouched');
is($block[1].name, 'foo', 'following sibling untouched');


# findPaths

my $mainBinding := QAST::Op.new(:op<bind>,
    QAST::Var.new(:name('&MAIN'), :scope<lexical>, :decl<var>),
    QAST::Block.new(
        QAST::Stmts.new(
            QAST::Var.new(:name('@ARGS'), :scope<lexical>, :decl<param>, :slurpy(1)),
        ),
        QAST::Stmts.new(),
    ),
);

my $fooBinding := QAST::Op.new(:op<bind>,
    QAST::Var.new(:name('&foo'), :scope<lexical>, :decl<var>),
    QAST::Block.new(
        QAST::Stmts.new(
            QAST::Var.new(:name('$bar'), :scope<lexical>, :decl<param>),
            QAST::Var.new(:name('$baz'), :scope<lexical>, :decl<var>),
        ),
        QAST::Stmts.new(
            QAST::Op.new(:op<eqaddr>,
                QAST::Var.new(:name('$bar'), :scope<lexical>),
                QAST::Var.new(:name('$baz'), :scope<lexical>),
            ),
        ),
    ),
);

my $ast := QAST::CompUnit.new(
    QAST::Block.new(
        QAST::Var.new(:name('@ARGS'), :scope<lexical>, :decl<param>, :slurpy(1)),
        QAST::Stmts.new(
            $fooBinding,
            $mainBinding,
        ),
        QAST::Stmts.new(),
    )
);

diag(dump($ast));

my @paths := findPaths(
    -> $n, @p {
        if @p {
            my $parent := @p[0];
            istype($parent, QAST::Op) && ($parent.op eq 'bind')
                && istype($n, QAST::Var) && $n.decl
        } else {
            0;
        }
    },
    $ast
);

is(+@paths, 2, 'nr of paths to defs')
    || diag(@paths);
is(@paths[0][0], $fooBinding[0],  '1st elem of 1st path found');
is(@paths[0][1], $fooBinding,     '2nd elem of 1st path found');
is(@paths[1][0], $mainBinding[0], '1st elem of 2nd path found');
is(@paths[1][1], $mainBinding,    '2nd elem of 2nd path found');


# fix_var_null_decls

@paths := findPaths(-> $n, @p { istype($n, QAST::Var) && !$n.decl }, $ast);
is(+@paths, 2, 'nr of paths to non-decl vars')
    || diag(@paths);
is(@paths[0][0].dump_extra_node_info, 'lexical $bar :decl()', 'var 1 before fix_var_null_decls');
is(@paths[1][0].dump_extra_node_info, 'lexical $baz :decl()', 'var 2 before fix_var_null_decls');

my $out := fix_var_null_decls($ast);
is($out, $ast, 'fix_var_null_decls returns its arg');

is(@paths[0][0].dump_extra_node_info, 'lexical $bar', 'var 1 after fix_var_null_decls');
is(@paths[1][0].dump_extra_node_info, 'lexical $baz', 'var 2 after fix_var_null_decls');



done();
