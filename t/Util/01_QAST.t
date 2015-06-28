#!nqp

use testing;
use Util;

use Util::QAST;

plan(201);



sub isa_nok($actual, $refutedType, str $desc) {
    my $result;
    if $refutedType =:= str {
        $result := !nqp::isstr($actual);
    } elsif $refutedType =:= int {
        $result := !nqp::isint($actual);
    } elsif $refutedType =:= num {
        $result := !nqp::isnum($actual);
    } else {
        $result := !istype($actual, $refutedType);
    }
    unless $result {
        $desc := $desc ~ "\n  # expected: something other than a " ~ $refutedType.HOW.name($refutedType)
                       ~ "\n  #      got: " ~ describe($actual)
        ;
    }
    ok($result, $desc);
}


sub isa_ok($actual, $expectedType, str $desc, *%attributes) {
    my $result;
    if $expectedType =:= str {
        $result := nqp::isstr($actual);
    } elsif $expectedType =:= int {
        $result := nqp::isint($actual);
    } elsif $expectedType =:= num {
        $result := nqp::isnum($actual);
    } else {
        $result := istype($actual, $expectedType);
    }
    if ($result && %attributes) {
        my $attrIt := nqp::iterator(%attributes);
        my $tests := -> {
            while $result && $attrIt {
                nqp::shift($attrIt);
                my $m := $attrIt.key;
                my $xv := $attrIt.value;
                if nqp::can($actual, $attrIt.key) {
                    my $av := nqp::callmethod($actual, $m);
                    my $d:= $desc ~ "\n  # expected: a " ~ $expectedType.HOW.name($expectedType)
                                    ~ " where .$m is " ~ describe($xv)
                                  ~ "\n  #   actual: " ~ describe($actual)
                    ;
                    unless is($av, $xv, $d) {
                        $desc := $d;
                        $result := 0;
                    }
                } else {
                    $desc := $desc ~ "\n  # expected: a " ~ $expectedType.HOW.name($expectedType)
                                        ~ " where .$m is " ~ describe($xv)
                                   ~ "\n  #   actual: " ~ describe($actual)
                                   ~ "\n  #      got: \"Cannot find method $m\""
                    ;
                    $result := ok(0, $desc);
                }
            }
            $result;
        };
        return passes_ok($tests, $desc);
    } else {
        $desc := $desc ~ "\n  # expected: a " ~ $expectedType.HOW.name($expectedType)
                       ~ "\n  #      got: " ~ describe($actual)
        ;
        return ok($result, $desc);
    }
}



sub mkBlockWithCATCH() {
    # {
    #   nqp::die('BOOM!');
    #   CATCH {
    #       nqp::say($!);
    #   }
    # }

    # ...gets compiled to:

    QAST::Op.new(:op<handle>,
        QAST::Stmts.new(
            QAST::Stmts.new(
                QAST::Op.new(:op<die>,
                    QAST::SVal.new(:value('BOOM!'))
                )
            ),
            QAST::Stmts.new(
                QAST::WVal.new(:value(NQPMu))
            )
        ),
        "CATCH",    # <--- yes, a literal str (rather than an SVal or such)
        QAST::Stmts.new(
            QAST::Op.new(:op<call>,
                QAST::Block.new(
                    QAST::Var.new(:name('$_'), :decl<param>),
                    QAST::Op.new(:op<bind>,
                        QAST::Var.new(:name('$!'), :decl<var>),
                        QAST::Var.new(:name('$_'), :decl(nqp::null_s)),
                    ),
                    QAST::Stmts.new(),
                    QAST::Stmts.new(
                        QAST::Stmts.new(
                            QAST::Op.new(:op<say>,
                                QAST::Var.new(:name('$!'), :decl(nqp::null_s))
                            )
                        )
                    ),
                ),
                QAST::Op.new(:op<exception>),
            ),
            QAST::VM.new(),
            QAST::WVal.new(:value(NQPMu))
        )
    );
};


{ # remove_bogusOpNames -------------------------------------------------------
    my $ast;

    $ast := mkBlockWithCATCH();
    lives_ok({ remove_bogusOpNames($ast) }, 'remove_bogusOpNames can cope with exception handlers')
        || diag(dump($ast));

    $ast := QAST::Op.new(:op<bind>, :name('&infix:<:=>'),
        QAST::Var.new(:name<foo>),
        QAST::SVal.new(:value<bar>)
    );
    $ast := remove_bogusOpNames($ast);
    isa_ok($ast, QAST::Op, :op<bind>, 'remove_bogusOpNames/bind operator stays the same');
    is($ast.name, '', 'remove_bogusOpNames/bind: attr .name unset');

    $ast := QAST::Op.new(:op<const>, :name('STAT_EXISTS'));
    $ast := remove_bogusOpNames($ast);
    isa_ok($ast, QAST::Op, :op<const>, :name('STAT_EXISTS'), 'remove_bogusOpNames/const untouched') || diag(dump($ast));

    $ast := QAST::Op.new(:op<lexotic>, :name('RETURN'));
    $ast := remove_bogusOpNames($ast);
    isa_ok($ast, QAST::Op, :op<lexotic>, :name('RETURN'), 'remove_bogusOpNames/lexotic untouched') || diag(dump($ast));

    $ast := QAST::Op.new(:op<control>, :name('last'));
    $ast := remove_bogusOpNames($ast);
    isa_ok($ast, QAST::Op, :op<control>, :name('last'), 'remove_bogusOpNames/control untouched') || diag(dump($ast));

    $ast := QAST::Op.new(:op<call>, :name('&foo'));
    $ast := remove_bogusOpNames($ast);
    isa_ok($ast, QAST::Op, :op<call>, :name('&foo'), 'remove_bogusOpNames/call untouched') || diag(dump($ast));

    $ast := QAST::Op.new(:op<callstatic>, :name('&foo'));
    $ast := remove_bogusOpNames($ast);
    isa_ok($ast, QAST::Op, :op<callstatic>, :name('&foo'), 'remove_bogusOpNames/callstatic untouched') || diag(dump($ast));

    $ast := QAST::Op.new(:op<callmethod>, :name('&foo'), QAST::Op.new(:op<null>));
    $ast := remove_bogusOpNames($ast);
    isa_ok($ast, QAST::Op, :op<callmethod>, :name('&foo'), 'remove_bogusOpNames/callmethod untouched') || diag(dump($ast));
}


{ # inline_simple_methods -----------------------------------------------------
    my $ast;

    $ast := mkBlockWithCATCH();
    lives_ok({ inline_simple_methods($ast) }, 'inline_simple_methods can cope with exception handlers')
        || diag(dump($ast));

    $ast := QAST::Op.new(:op<callmethod>, :name<op>,
        QAST::Var.new(:name('$node'))
    );
    $ast := inline_simple_methods($ast);
    isa_ok($ast, QAST::Op, :op<callmethod>, :name<op>, 'inline_simple_methods/call to method .op left untouched');

    $ast := QAST::Op.new(:op<callmethod>, :name<pop>,
        QAST::Var.new(:name('@xs'))
    );
    $ast := inline_simple_methods($ast);
    isa_ok($ast, QAST::Op, :op<pop>, :name(''), 'inline_simple_methods/call to method .pop ~> Op pop');

    $ast := QAST::Op.new(:op<callmethod>, :name<push>,
        QAST::Var.new(:name('@xs')),
        QAST::SVal.new(:value<foo>)
    );
    $ast := inline_simple_methods($ast);
    isa_ok($ast, QAST::Op, :op<push>, :name(''), 'inline_simple_methods/call to method .push ~> Op push');

    $ast := QAST::Op.new(:op<callmethod>, :name<shift>,
        QAST::Var.new(:name('@xs'))
    );
    $ast := inline_simple_methods($ast);
    isa_ok($ast, QAST::Op, :op<shift>, :name(''), 'inline_simple_methods/call to method .shift ~> Op shift');

    $ast := QAST::Op.new(:op<callmethod>, :name<unshift>,
        QAST::Var.new(:name('@xs')),
        QAST::SVal.new(:value<foo>)
    );
    $ast := inline_simple_methods($ast);
    isa_ok($ast, QAST::Op, :op<unshift>, :name(''), 'inline_simple_methods/call to method .unshift ~> Op unshift');

    $ast := QAST::Op.new(:op<callmethod>, :name<key>,
        QAST::Op.new(:op<iterator>, 
            QAST::Var.new(:name('%xs'))
        )
    );
    $ast := inline_simple_methods($ast);
    isa_ok($ast, QAST::Op, :op<iterkey_s>, :name(''), 'inline_simple_methods/call to method .key ~> Op iterkey_s');

    $ast := QAST::Op.new(:op<callmethod>, :name<value>,
        QAST::Op.new(:op<iterator>, 
            QAST::Var.new(:name('%xs'))
        )
    );
    $ast := inline_simple_methods($ast);
    isa_ok($ast, QAST::Op, :op<callmethod>, :name<value>, 'inline_simple_methods/call to method .value *untouched* (!)');

}


my $ast := mkBlockWithCATCH();

ok( istype($ast, QAST::Node), 'mkBlockWithCATCH returns a QAST::Node' )
    || diag($ast) && nqp::exit(1);


my $w := QAST::WVal.new(:value(NQPMu));
is(dump($w), '─◙ WVal NQPMu', 'dump world value NQPMu');

my $vwf := QAST::VarWithFallback.new(:scope<positional>, :fallback(QAST::WVal.new(:value(NQPMu))), :decl(nqp::null_s));
is(dump($vwf), '─○┬VarWithFallback positional :fallback(WVal NQPMu)', 'dump VarWithFallback') || diag(dump($vwf));
is(dump($vwf, :oneLine), '(VarWithFallback positional :fallback(WVal NQPMu))', 'dump VarWithFallback :oneLine');

my $s := QAST::SVal.new(:value<bar>);
is(dump($s), '─◙ SVal "bar"', 'dump str constant "bar"');
$s.value('');
is(dump($s), '─◙ SVal ""', 'dump str constant ""');

my $i := QAST::IVal.new(:value(23));
is(dump($i), '─◙ IVal 23', 'dump int constant 23');
$i.value(0);
is(dump($i), '─◙ IVal 0', 'dump int constant 0');

my $n := QAST::NVal.new(:value(3.1415));
is(dump($n), '─◙ NVal 3.1415', 'dump num constant 3.1415');
$n.value(nqp::inf);
is(dump($n), '─◙ NVal Inf', 'dump num constant inf');
$n.value(0.0);
is(dump($n), '─◙ NVal 0', 'dump num constant 0.0');

my $nullop := QAST::Op.new(:op<null>);
is(dump($nullop), '──null', 'dump Op null');
is(dump($nullop, :indent('    ')), '    ──null', 'dump Op null with indent');
is(dump($nullop, :oneLine), '(null)', 'dump Op null on one line');


my $v := QAST::Var.new(:name<foo>);
is(dump($v), '─○ foo :decl()', 'dump Var w/out explicit scope');
$v.decl(nqp::null_s);   # bug in QAST::Var
is(dump($v), '─○ foo', 'dump Var w/out explicit scope and :decl set to null_s');

$v.scope('contextual');
is(dump($v), '─○ contextual foo', 'dump Var with explicit scope "contextual"');

$v.scope('local');
is(dump($v), '─○ local foo', 'dump Var with explicit scope "local"');

$v.scope('lexical');
is(dump($v), '─○ foo', 'dump Var with explicit scope "lexical"');


my $stmts := QAST::Stmts.new($nullop, $v);
is(dump($stmts),
             "──:Stmts"
         ~ "\n  ├─null"
         ~ "\n  └○ foo", 
    'dump Stmts with children uses single vertical line to connect children');
dies_ok( { ~$stmts }, 'stringifying QAST::Stmts as is');
$stmts.HOW.mixin($stmts, StrByDump);
is(~$stmts, 
             "──:Stmts+\{StrByDump}"
         ~ "\n  ├─null"
         ~ "\n  └○ foo", 
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
         ~ "\n  ╙○ foo", 
    'dump Block with children uses double vertical line to connect children');
is(dump($b, :indent('# ')), 
            "# ──:Block"
        ~ "\n#   ╟─null"
        ~ "\n#   ╙○ foo", 
    'dump Block with children with indent uses double vertical line to connect children');
is(dump($b, :oneLine), "((Block) (null) (foo))", 'dump Block with children on one line');



# role StrByDump
dies_ok( { ~$b }, 'stringifying QAST::Block as is');
$b.HOW.mixin($b, StrByDump);
is(~$b,  
           "──:Block+\{StrByDump}"
         ~ "\n  ╟─null"
         ~ "\n  ╙○ foo", 
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

my $stmts_needed_main := QAST::Stmts.new(    # this Stmts *cannot* be dropped because it's under an Op and has more than 1 child
    QAST::Op.new(:op<add_i>,
        QAST::IVal.new(:value(1)),
        QAST::Op.new(:op<atpos>,
            QAST::Var.new(:name('@ARGS'), :scope<lexical>),
            QAST::IVal.new(:value(1)),
        ),
    ),
    QAST::Op.new(:op<add_i>,
        QAST::IVal.new(:value(1)),
        QAST::Op.new(:op<atpos>,
            QAST::Var.new(:name('@ARGS'), :scope<lexical>),
            QAST::IVal.new(:value(1)),
        ),
    ),
);

my $mainBinding := QAST::Op.new(:op<bind>,
    QAST::Var.new(:name('&MAIN'), :scope<lexical>, :decl<var>),
    QAST::Block.new(
        QAST::Stmts.new(
            QAST::Var.new(:name('@ARGS'), :scope<lexical>, :decl<param>, :slurpy(1)),
        ),
        QAST::Stmts.new(    # this Stmts can be dropped
            QAST::Op.new(:op<iseq_i>,
                QAST::IVal.new(:value(2)),
                $stmts_needed_main
            ),
        ),
    ),
);

my $stmts_needed_foo := QAST::Stmts.new(:resultchild(0),    # this Stmts *cannot* be dropped due to its :resultchild
    QAST::Op.new(:op<eqaddr>,
        QAST::Var.new(:name('$bar')),   # bug in QAST::Var: not giving explicit scope yields scope "" (rather than nqp::null_s or the default "lexical")
        QAST::Var.new(:name('$baz'), :scope<lexical>),
    ),
    QAST::Var.new(:name('$bar'), :scope<lexical>),
    QAST::VarWithFallback.new(
        :scope<contextual>, 
        :name('$*UNIT'), 
        :fallback(
            QAST::Op.new(:op<ifnull>,
                QAST::VarWithFallback.new(
                    :scope<associative>, 
                    :fallback(QAST::WVal.new(:value(NQPMu))),
                    QAST::Op.new(:op<who>, QAST::WVal.new(:value(GLOBALish))),
                    QAST::SVal.new(:value('$UNIT'))
                ),
                QAST::Op.new(:op<die_s>,
                    SVal.new(:value('Contextual $*UNIT not found'))
                )
            )
        )
    )
);

my $fooBinding := QAST::Op.new(:op<bind>,
    QAST::Var.new(:name('&foo'), :scope<lexical>, :decl<var>),
    QAST::Block.new(
        QAST::Stmts.new(
            QAST::Var.new(:name('$bar'), :scope<lexical>, :decl<param>),
            QAST::Var.new(:name('$baz'), :scope<lexical>, :decl<var>),
        ),
        $stmts_needed_foo,
    ),
);

$ast := QAST::CompUnit.new(
    QAST::Block.new(
        QAST::Var.new(:name('@ARGS'), :scope<lexical>, :decl<param>, :slurpy(1)),
        QAST::Stmts.new(:resultchild(1),    # this Stmts can be dropped since its :resultchild is the last anyways
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


# fix_var_attrs

@paths := findPaths(-> $n, @p { istype($n, QAST::Var) && !$n.decl }, $ast);
is(+@paths, 6, 'nr of paths to non-decl vars')
    || diag(@paths);


my $out := fix_var_attrs($ast);
is($out, $ast, 'fix_var_attrs returns its arg');

is(@paths[0][0].dump_extra_node_info, 'lexical $bar', 'var 1 after fix_var_attrs');
is(@paths[1][0].dump_extra_node_info, 'lexical $baz', 'var 2 after fix_var_attrs');
is(@paths[2][0].dump_extra_node_info, 'lexical $bar', 'var 3 after fix_var_attrs');
is(@paths[3][0].dump_extra_node_info, 'contextual $*UNIT', 'var 4 after fix_var_attrs');
is(@paths[3][0].fallback[0].dump_extra_node_info, 'associative', ' fix_var_attrs recurses into :fallback (inside var 4\'s fallback)');
is(@paths[4][0].dump_extra_node_info, 'lexical @ARGS', 'var 5 after fix_var_attrs');
is(@paths[5][0].dump_extra_node_info, 'lexical @ARGS', 'var 6 after fix_var_attrs');


# drop_Stmts ------------------------------------------------------------------

$out := drop_Stmts($ast);

is($out, $ast, 'drop_Stmts returns its arg');
my @stmts_left := findPaths(-> $n, @p { istype($n, QAST::Stmts) }, $ast);
is(+@stmts_left, 2, 'drop_Stmts removed all Stmts nodes except those with :resultchild')
  || diag(dump($ast));

is(@stmts_left[0][0], $stmts_needed_foo, '1st Stmts node left in')
    || diag(dump(@stmts_left[0][0]));
is(@stmts_left[1][0], $stmts_needed_main, '2nd Stmts node left in')
    || diag(dump(@stmts_left[1][0]));


for QAST::Stmts, QAST::Stmt -> $STMT_KIND {

    my $resultVar := QAST::Var.new(:name<$x>);
    my $stmts_inner := QAST::Stmts.new(
        QAST::Op.new(:op<bind>,
            QAST::Var.new(:name<$x>),
            QAST::Op.new(:op<add_i>,
                QAST::Var.new(:name<$x>),
                QAST::IVal.new(:value(1)),
            ),
        ),
        $resultVar,
    );

    my $stmt := QAST::Stmt.new( # singular!
        QAST::Op.new(:op<say>,
            QAST::Var.new(:name<$x>),
        )
    );
    $stmt.annotate('NOTE', 'Stmt (singular!) is not dropped');

    my $stmts_needed := $STMT_KIND.new(:resultchild(1),
        $stmt,
        $stmts_inner,
    );
    $stmts_needed.annotate('NOTE', ':resultchild needs fixup if inner Stmts is dropped');

    my $block := QAST::Block.new(
        QAST::Var.new(:name<$x>, :decl<param>),
        QAST::Op.new(:op<say>,
            $stmts_needed
        ),
    );
    my $stmts_topmost := QAST::Stmts.new($block);
    my $ast := $stmts_topmost;
    my $STMT_WHAT := $STMT_KIND.HOW.name($STMT_KIND);
    #diag("check :resultChild fixup in $STMT_WHAT\n" ~ dump($ast));

    sub resultterm($node) {
        nqp::die('"resultterm expects either a Block, Stmts or Stmt - got ' ~ describe($node))
            unless istype($node, QAST::Block, QAST::Stmts, QAST::Stmt);
        my $i := istype($node, QAST::Block) || !nqp::isint($node.resultchild)
            ?? nqp::elems($node.list) - 1
            !! $node.resultchild;
        $i < 0
            ?? NQPMu
            !! $node[$i];
    }

    is(resultterm($stmts_inner), $resultVar, 'result term of the inner Stmts (sanity)')
        || diag(dump($stmts_inner));
    is(resultterm($stmts_needed), $stmts_inner, "result term of the outer $STMT_WHAT (sanity)")
        || diag(dump($stmts_needed));

    $ast := drop_Stmts($ast);

    is($ast, $block, 'topmost Stmts is dropped') || diag(dump($ast));

    is($ast[1][0], $stmts_needed, "$STMT_WHAT under `say` is not dropped because it has > 1 children")
        || diag(dump($ast));
    is(resultterm($stmts_needed), $resultVar, 'either :resultchild is set to correct value or deleted')
        || diag(dump($ast));
    is($stmts_needed[0], $stmt, 'Stmt (singular!) nodes are not dropped')
        || diag(dump($ast));

    #diag(dump($ast));
}


{ # drop_Stmts (2) ------------------------------------------------------------
    my $ast := mkBlockWithCATCH();

    # {
    #   nqp::die('BOOM!');
    #   CATCH {
    #       nqp::say($!);
    #   }
    # }

    # ...gets compiled to:

    # BEFORE:                               # AFTER:                    
    #
    #──handle                               # ──handle                  
    #  ├─:Stmts                             #   ├─:Stmts                
    #  │ ├─:Stmts
    #  │ │ └─die                            #   │ ├─die                 
    #  │ │   └◙ SVal "BOOM!"                #   │ │ └◙ SVal "BOOM!"     
    #  │ └─:Stmts
    #  │   └◙ WVal NQPMu                    #   │ └◙ WVal NQPMu         
    #  ├► "CATCH" (str)                     #   ├► "CATCH" (str)        
    #  └─:Stmts                             #   └─:Stmts                
    #    ├─call                             #     ├─call                
    #    │ ├─:Block                         #     │ ├─:Block            
    #    │ │ ╟○ $_ :decl(param)             #     │ │ ╟○ $_ :decl(param)
    #    │ │ ╟─bind                         #     │ │ ╟─bind            
    #    │ │ ║ ├○ $! :decl(var)             #     │ │ ║ ├○ $! :decl(var)
    #    │ │ ║ └○ $_                        #     │ │ ║ └○ $_           
    #    │ │ ╟─:Stmts
    #    │ │ ╙─:Stmts
    #    │ │   └─:Stmts
    #    │ │     └─say                      #     │ │ ╙─say             
    #    │ │       └○ $!                    #     │ │   └○ $!           
    #    │ └─exception                      #     │ └─exception         
    #    ├─:VM                              #     ├─:VM                 
    #    └◙ WVal NQPMu                      #     └◙ WVal NQPMu         

    my $out;
    lives_ok({ $out := drop_Stmts($ast) }, 'drop_Stmts can cope with exception handlers')
        || diag(dump($ast));

    my $bind1 := QAST::Op.new(:op<bind>,
        QAST::Var.new(:name('$x')),
        QAST::IVal.new(:value(7))
    );
    my $bind2 := QAST::Op.new(:op<bind>,
        QAST::Var.new(:name('$x')),
        QAST::Op.new(:op<add_i>,
            QAST::Var.new(:name('$x')),
            QAST::IVal.new(:value(42))
        )
    );
    my $wval_mu := QAST::WVal.new(:value(NQPMu));
    my $bind3 := QAST::Op.new(:op<bind>,
        QAST::Var.new(:name('$x')),
        QAST::Op.new(:op<sub_i>,
            QAST::Var.new(:name('$x')),
            QAST::IVal.new(:value(23))
        )
    );
    my $outer := QAST::Stmts.new(:resultchild(1), # not removed due to resultchild
        QAST::Stmts.new(    # to be removed - but parent's resultchild needs adjustment
            $bind1,
            $bind2,
        ),
        $wval_mu,
        $bind3
    );
    $ast := QAST::CompUnit.new($outer);

    #diag(dump($ast));
    $ast := drop_Stmts($ast);
    #diag(dump($ast));

    is( $ast[0], $outer, 'outer Stmts not dropped due to :resultchild') || diag(dump($ast[0]));
    is( $outer[0], $bind1, 'inner Stmts has been dropped (a)') || diag(dump($outer[0]));
    is( $outer[1], $bind2, 'inner Stmts has been dropped (b)') || diag(dump($outer[1]));
    is( $outer[2], $wval_mu, 'inner Stmts has been dropped (c)') || diag(dump($outer[2]));
    is( $outer[3], $bind3, 'inner Stmts has been dropped (d)') || diag(dump($outer[3]));
    is( $outer.resultchild, 2, 'resultchild of outer Stmts is fixed') || diag(dump($outer));
}


{ # replace_assoc_and_pos_scoped ----------------------------------------------
    my $ast;

    $ast := mkBlockWithCATCH();
    lives_ok({ replace_assoc_and_pos_scoped($ast) }, 'replace_assoc_and_pos_scoped can cope with exception handlers')
        || diag(dump($ast));


    # `@xs[0]`
    $ast := QAST::VarWithFallback.new(:scope<positional>, :fallback(QAST::WVal.new(:value(NQPMu))),
        QAST::Var.new(:name('@xs')),
        QAST::IVal.new(:value(0))
    );
    #diag(dump($ast));
    $ast := replace_assoc_and_pos_scoped($ast);
    isa_ok( $ast,       QAST::Op, :op<ifnull>,      '"positional" scoped VarWithFallback ~> Op ifnull ...') || diag(dump($ast));
    isa_ok( $ast[0],    QAST::Op, :op<atpos>,       '"positional" scoped VarWithFallback ~> Op ifnull atpos ...') || diag(dump($ast));
    isa_ok( $ast[1],    QAST::WVal, :value(NQPMu),  '"positional" scoped VarWithFallback ~> Op ifnull ... WVal(NQPMu)') || diag(dump($ast));
    isa_ok( $ast[0][0], QAST::Var, :name('@xs'),    '"positional" scoped VarWithFallback, atpos\' 1st child') || diag(dump($ast));
    isa_ok( $ast[0][1], QAST::IVal, :value(0),      '"positional" scoped VarWithFallback, atpos\' 2nd child') || diag(dump($ast));

    # `%xs<somekey>`
    $ast := QAST::VarWithFallback.new(:scope<associative>, :fallback(QAST::WVal.new(:value(NQPMu))),
        QAST::Var.new(:name('%xs')),
        QAST::SVal.new(:value<somekey>)
    );
    #diag(dump($ast));
    $ast := replace_assoc_and_pos_scoped($ast);
    isa_ok( $ast,       QAST::Op, :op<ifnull>,       '"associative" scoped VarWithFallback ~> Op ifnull ...') || diag(dump($ast));
    isa_ok( $ast[0],    QAST::Op, :op<atkey>,        '"associative" scoped VarWithFallback ~> Op ifnull atkey ...') || diag(dump($ast));
    isa_ok( $ast[1],    QAST::WVal, :value(NQPMu),   '"associative" scoped VarWithFallback ~> Op ifnull ... WVal(NQPMu)') || diag(dump($ast));
    isa_ok( $ast[0][0], QAST::Var, :name('%xs'),     '"associative" scoped VarWithFallback, atkey\'s 1st child') || diag(dump($ast));
    isa_ok( $ast[0][1], QAST::SVal, :value<somekey>, '"associative" scoped VarWithFallback, atkey\'s 2nd child') || diag(dump($ast));

    $ast := QAST::Stmts.new(    # `say(@xs[0])`
        QAST::Op.new(:op<say>,
            QAST::VarWithFallback.new(:scope<positional>, :fallback(QAST::WVal.new(:value(NQPMu))),
                QAST::Var.new(:name('@xs')),
                QAST::IVal.new(:value(0))
            )
        )
    );
    #diag(dump($ast));
    replace_assoc_and_pos_scoped($ast);
    {
        my $n := $ast[0][0];
        isa_nok($n, QAST::SpecialArg, 'filled in Op should not be SpecialArg when original wasn\'t one') || diag(dump($ast));
        isa_ok( $n,       QAST::Op, :op<ifnull>,     '"positional" scoped VarWithFallback ~> Op ifnull ...') || diag(dump($ast));
        isa_ok( $n[0],    QAST::Op, :op<atpos>,      '"positional" scoped VarWithFallback ~> Op ifnull atpos ...') || diag(dump($ast));
        isa_ok( $n[1],    QAST::WVal, :value(NQPMu), '"positional" scoped VarWithFallback ~> Op ifnull ... WVal(NQPMu)') || diag(dump($ast));
        isa_ok( $n[0][0], QAST::Var, :name('@xs'),   '"positional" scoped VarWithFallback ~> atpos\'s 1st child') || diag(dump($ast));
        isa_ok( $n[0][1], QAST::IVal, :value(0),     '"positional" scoped VarWithFallback ~> atpos\'s 2nd child') || diag(dump($ast));
    }

    $ast := QAST::Stmts.new(    # `say(%xs<somekey>)`
        QAST::Op.new(:op<say>,
            QAST::VarWithFallback.new(:scope<associative>, :fallback(QAST::WVal.new(:value(NQPMu))),
                QAST::Var.new(:name('%xs')),
                QAST::SVal.new(:value<somekey>)
            )
        )
    );
    #diag(dump($ast));
    replace_assoc_and_pos_scoped($ast);
    {
        my $n := $ast[0][0];
        isa_nok($n, QAST::SpecialArg, 'filled in Op should not be SpecialArg when original wasn\'t one') || diag(dump($ast));
    }

    $ast := QAST::Stmts.new(    # `foo(:bar(@xs[0]))`
        QAST::Op.new(:op<call>, :name('&foo'),
            QAST::VarWithFallback.new(:scope<positional>, :named<bar>, :fallback(QAST::WVal.new(:value(NQPMu))),
                QAST::Var.new(:name('@xs')),
                QAST::IVal.new(:value(0))
            )
        )
    );
    #diag(dump($ast));
    replace_assoc_and_pos_scoped($ast);
    {
        my $n := $ast[0][0];
        isa_ok( $n, QAST::SpecialArg, :named<bar>, :flat(0), 'filled in Op should be SpecialArg when original was one') || diag(dump($ast));
        isa_ok( $n,       QAST::Op, :op<ifnull>,     '"positional" scoped VarWithFallback as named arg ~> Op ifnull ...') || diag(dump($ast));
        isa_ok( $n[0],    QAST::Op, :op<atpos>,      '"positional" scoped VarWithFallback as named arg ~> Op ifnull atpos ...') || diag(dump($ast));
        isa_ok( $n[1],    QAST::WVal, :value(NQPMu), '"positional" scoped VarWithFallback as named arg ~> Op ifnull ... WVal(NQPMu)') || diag(dump($ast));
        isa_ok( $n[0][0], QAST::Var, :name('@xs'),   '"positional" scoped VarWithFallback as named arg ~> atpos\'s 1st child') || diag(dump($ast));
        isa_ok( $n[0][1], QAST::IVal, :value(0),     '"positional" scoped VarWithFallback as named arg ~> atpos\'s 2nd child') || diag(dump($ast));
    }


    $ast := QAST::Stmts.new(    # `foo(:bar(%xs<somekey>))`
        QAST::Op.new(:op<call>, :name('&foo'),
            QAST::VarWithFallback.new(:scope<associative>, :named<bar>, :fallback(QAST::WVal.new(:value(NQPMu))),
                QAST::Var.new(:name('%xs')),
                QAST::SVal.new(:value<somekey>)
            )
        )
    );
    #diag(dump($ast));
    replace_assoc_and_pos_scoped($ast);
    {
        my $n := $ast[0][0];
        isa_ok( $n, QAST::SpecialArg, :named<bar>, :flat(0), 'filled in Op should be SpecialArg when original was one') || diag(dump($ast));
        isa_ok( $n,       QAST::Op, :op<ifnull>,        '"associative" scoped VarWithFallback as named arg ~> Op ifnull ...') || diag(dump($ast));
        isa_ok( $n[0],    QAST::Op, :op<atkey>,         '"associative" scoped VarWithFallback as named arg ~> Op ifnull atkey ...') || diag(dump($ast));
        isa_ok( $n[1],    QAST::WVal, :value(NQPMu),    '"associative" scoped VarWithFallback as named arg ~> Op ifnull ... WVal(NQPMu)') || diag(dump($ast));
        isa_ok( $n[0][0], QAST::Var, :name('%xs'),      '"associative" scoped VarWithFallback as named arg ~> atkey\'s 1st child') || diag(dump($ast));
        isa_ok( $n[0][1], QAST::SVal, :value<somekey>,  '"associative" scoped VarWithFallback as named arg ~> atkey\'s 2nd child') || diag(dump($ast));
    }


    $ast := QAST::Stmts.new(    # `qumbl(|@xs[0])`
        QAST::Op.new(:op<call>, :name('&qumbl'),
            QAST::VarWithFallback.new(:scope<positional>, :flat, :fallback(QAST::WVal.new(:value(NQPMu))),
                QAST::Var.new(:name('@xs')),
                QAST::IVal.new(:value(0))
            )
        )
    );
    #diag(dump($ast));
    replace_assoc_and_pos_scoped($ast);
    {
        my $n := $ast[0][0];
        isa_ok( $n, QAST::SpecialArg, :named(NQPMU), :flat(1), 'filled in Op should be SpecialArg when original was one') || diag(dump($ast));
        isa_ok( $n,       QAST::Op, :op<ifnull>,     '"positional" scoped VarWithFallback as flat arg ~> Op ifnull ...') || diag(dump($ast));
        isa_ok( $n[0],    QAST::Op, :op<atpos>,      '"positional" scoped VarWithFallback as flat arg ~> Op ifnull atpos ...') || diag(dump($ast));
        isa_ok( $n[1],    QAST::WVal, :value(NQPMu), '"positional" scoped VarWithFallback as flat arg ~> Op ifnull ... WVal(NQPMu)') || diag(dump($ast));
        isa_ok( $n[0][0], QAST::Var, :name('@xs'),   '"positional" scoped VarWithFallback as flat arg ~> atpos\'s 1st child') || diag(dump($ast));
        isa_ok( $n[0][1], QAST::IVal, :value(0),     '"positional" scoped VarWithFallback as flat arg ~> atpos\'s 2nd child') || diag(dump($ast));
    }


    $ast := QAST::Stmts.new(    # `qumbl(|%xs<somekey>)`
        QAST::Op.new(:op<call>, :name('&qumbl'),
            QAST::VarWithFallback.new(:scope<associative>, :flat, :fallback(QAST::WVal.new(:value(NQPMu))),
                QAST::Var.new(:name('%xs')),
                QAST::SVal.new(:value<somekey>)
            )
        )
    );
    #diag(dump($ast));
    replace_assoc_and_pos_scoped($ast);
    {
        my $n := $ast[0][0];
        isa_ok( $n, QAST::SpecialArg, :named(NQPMU), :flat(1), 'filled in Op should be SpecialArg when original was one') || diag(dump($ast));
        isa_ok( $n,       QAST::Op, :op<ifnull>,        '"associative" scoped VarWithFallback as flat arg ~> Op ifnull ...') || diag(dump($ast));
        isa_ok( $n[0],    QAST::Op, :op<atkey>,         '"associative" scoped VarWithFallback as flat arg ~> Op ifnull atkey ...') || diag(dump($ast));
        isa_ok( $n[1],    QAST::WVal, :value(NQPMu),    '"associative" scoped VarWithFallback as flat arg ~> Op ifnull ... WVal(NQPMu)') || diag(dump($ast));
        isa_ok( $n[0][0], QAST::Var, :name('%xs'),      '"associative" scoped VarWithFallback as flat arg ~> atkey\'s 1st child') || diag(dump($ast));
        isa_ok( $n[0][1], QAST::SVal, :value<somekey>,  '"associative" scoped VarWithFallback as flat arg ~> atkey\'s 2nd child') || diag(dump($ast));
    }


    $ast := QAST::Stmts.new(    # `qumbl(:bar(@xs[0] := 5))`
        QAST::Op.new(:op<call>, :name('&qumbl'),
            QAST::Op.new(:op<bind>, :named<bar>, 
                QAST::VarWithFallback.new(:scope<positional>, :fallback(QAST::WVal.new(:value(NQPMu))),
                    QAST::Var.new(:name('@xs')),
                    QAST::IVal.new(:value(0))
                ),
                QAST::IVal.new(:value(5))
            )
        )
    );
    #diag(dump($ast));
    replace_assoc_and_pos_scoped($ast);
    {
        my $n := $ast[0][0];
        isa_ok( $n, QAST::SpecialArg, :named<bar>, :flat(0), 'filled in Op should be SpecialArg when original was one') || diag(dump($ast));
        isa_ok( $n,     QAST::Op, :op<bindpos>,     '"positional" scoped VarWithFallback as named arg under bind ~> Op bindpos ...') || diag(dump($ast));
        isa_ok( $n[0],  QAST::Var, :name('@xs'),    '"positional" scoped VarWithFallback as named arg under bind ~> bindpos\'s 1st child') || diag(dump($ast));
        isa_ok( $n[1],  QAST::IVal, :value(0),      '"positional" scoped VarWithFallback as named arg under bind ~> bindpos\'s 2nd child') || diag(dump($ast));
        isa_ok( $n[2],  QAST::IVal, :value(5),      '"positional" scoped VarWithFallback as named arg under bind ~> bindpos\'s 3rd child') || diag(dump($ast));
    }


    $ast := QAST::Stmts.new(    # `qumbl(:bar(%xs<somekey> := 5))`
        QAST::Op.new(:op<call>, :name('&qumbl'),
            QAST::Op.new(:op<bind>, :named<bar>, 
                QAST::VarWithFallback.new(:scope<associative>, :fallback(QAST::WVal.new(:value(NQPMu))),
                    QAST::Var.new(:name('%xs')),
                    QAST::SVal.new(:value<somekey>)
                ),
                QAST::IVal.new(:value(5))
            )
        )
    );
    #diag(dump($ast));
    replace_assoc_and_pos_scoped($ast);
    {
        my $n := $ast[0][0];
        isa_ok( $n, QAST::SpecialArg, :named<bar>, :flat(0), 'filled in Op should be SpecialArg when original was one') || diag(dump($ast));
        isa_ok( $n,     QAST::Op, :op<bindkey>,      '"associative" scoped VarWithFallback as named arg under bind ~> Op bindkey ...') || diag(dump($ast));
        isa_ok( $n[0],  QAST::Var, :name('%xs'),     '"associative" scoped VarWithFallback as named arg under bind ~> bindkey\'s 1st child') || diag(dump($ast));
        isa_ok( $n[1],  QAST::SVal, :value<somekey>, '"associative" scoped VarWithFallback as named arg under bind ~> bindkey\'s 2nd child') || diag(dump($ast));
        isa_ok( $n[2],  QAST::IVal, :value(5),       '"associative" scoped VarWithFallback as named arg under bind ~> bindkey\'s 3rd child') || diag(dump($ast));
    }


    $ast := QAST::Stmts.new(    # `qumbl(|@xs[0] := [23, 42]))`
        QAST::Op.new(:op<call>, :name('&qumbl'),
            QAST::Op.new(:op<bind>, :flat,
                QAST::VarWithFallback.new(:scope<positional>, :fallback(QAST::WVal.new(:value(NQPMu))),
                    QAST::Var.new(:name('@xs')),
                    QAST::IVal.new(:value(0))
                ),
                QAST::Op.new(:op<list>,
                    QAST::IVal.new(:value(23)),
                    QAST::IVal.new(:value(42))
                )
            )
        )
    );
    #diag(dump($ast));
    replace_assoc_and_pos_scoped($ast);
    {
        my $n := $ast[0][0];
        isa_ok( $n, QAST::SpecialArg, :named(NQPMu), :flat(1), 'filled in Op should be SpecialArg when original was one') || diag(dump($ast));
        isa_ok( $n,         QAST::Op, :op<bindpos>,     '"positional" scoped VarWithFallback as flat arg under bind ~> Op bindpos ...') || diag(dump($ast));
        isa_ok( $n[0],      QAST::Var, :name('@xs'),    '"positional" scoped VarWithFallback as flat arg under bind ~> bindpos\'s 1st child') || diag(dump($ast));
        isa_ok( $n[1],      QAST::IVal, :value(0),      '"positional" scoped VarWithFallback as flat arg under bind ~> bindpos\'s 2nd child') || diag(dump($ast));
        isa_ok( $n[2],      QAST::Op, :op<list>,        '"positional" scoped VarWithFallback as flat arg under bind ~> bindpos\'s 3rd child') || diag(dump($ast));
        isa_ok( $n[2][0],   QAST::IVal, :value(23),     '"positional" scoped VarWithFallback as flat arg under bind ~> lists\'s 1st child') || diag(dump($ast));
        isa_ok( $n[2][1],   QAST::IVal, :value(42),     '"positional" scoped VarWithFallback as flat arg under bind ~> lists\'s 2nd child') || diag(dump($ast));
    }


    $ast := QAST::Stmts.new(    # `qumbl(|%xs<somekey> := hash(:foo(4711)))`
        QAST::Op.new(:op<call>, :name('&qumbl'),
            QAST::Op.new(:op<bind>, :flat,
                QAST::VarWithFallback.new(:scope<associative>, :fallback(QAST::WVal.new(:value(NQPMu))),
                    QAST::Var.new(:name('%xs')),
                    QAST::SVal.new(:value<somekey>)
                ),
                QAST::Op.new(:op<hash>,
                    QAST::SVal.new(:value<foo>),
                    QAST::IVal.new(:value(4711))
                )
            )
        )
    );
    #diag(dump($ast));
    replace_assoc_and_pos_scoped($ast);
    {
        my $n := $ast[0][0];
        isa_ok( $n, QAST::SpecialArg, :named(NQPMu), :flat(1), 'filled in Op should be SpecialArg when original was one') || diag(dump($ast));
        isa_ok( $n,         QAST::Op, :op<bindkey>,     '"associative" scoped VarWithFallback as flat arg under bind ~> Op bindkey ...') || diag(dump($ast));
        isa_ok( $n[0],      QAST::Var, :name('%xs'),    '"associative" scoped VarWithFallback as flat arg under bind ~> bindkey\'s 1st child') || diag(dump($ast));
        isa_ok( $n[1],      QAST::SVal, :value<somekey>,'"associative" scoped VarWithFallback as flat arg under bind ~> bindkey\'s 2nd child') || diag(dump($ast));
        isa_ok( $n[2],      QAST::Op, :op<hash>,        '"associative" scoped VarWithFallback as flat arg under bind ~> bindkey\'s 3rd child') || diag(dump($ast));
        isa_ok( $n[2][0],   QAST::SVal, :value<foo>,    '"associative" scoped VarWithFallback as flat arg under bind ~> hash\'s 1st child') || diag(dump($ast));
        isa_ok( $n[2][1],   QAST::IVal, :value(4711),   '"associative" scoped VarWithFallback as flat arg under bind ~> hash\'s 2nd child') || diag(dump($ast));
    }


    my $bazVar := QAST::Var.new(:name('$baz'));
    $ast := QAST::Stmts.new(    # `qumbl(|$baz := @xs[0])`
        QAST::Op.new(:op<call>, :name('&qumbl'),
            QAST::Op.new(:op<bind>, :flat,
                $bazVar,
                QAST::VarWithFallback.new(:scope<positional>, :fallback(QAST::WVal.new(:value(NQPMu))),
                    QAST::Var.new(:name('@xs')),
                    QAST::IVal.new(:value(0))
                ),
            )
        )
    );
    #diag(dump($ast));
    replace_assoc_and_pos_scoped($ast);
    {
        my $n := $ast[0][0];
        isa_ok( $n,     QAST::SpecialArg, :named(NQPMu), :flat(1),  '"positional" scoped VarWithFallback on rhs under bind / bind stays SpecialArg if it was one') || diag(dump($ast));
        isa_ok( $n,     QAST::Op, :op<bind>,                        '"positional" scoped VarWithFallback on rhs under bind / bind stays bind') || diag(dump($ast));
        is(     $n[0],  $bazVar,                            '"positional" scoped VarWithFallback on rhs under bind ~> lhs unchanged') || diag(dump($ast));
        isa_ok( $n[1],          QAST::Op, :op<ifnull>,      '"positional" scoped VarWithFallback on rhs under bind ~> Op ifnull') || diag(dump($ast));
        isa_ok( $n[1][0],       QAST::Op, :op<atpos>,       '"positional" scoped VarWithFallback on rhs under bind ~> Op ifnull atpos ...') || diag(dump($ast));
        isa_ok( $n[1][1],       QAST::WVal, :value(NQPMu),  '"positional" scoped VarWithFallback on rhs under bind ~> Op ifnull ... WVal(NQPMu)') || diag(dump($ast));
        isa_ok( $n[1][0][0],    QAST::Var, :name('@xs'),    '"positional" scoped VarWithFallback on rhs under bind ~> atpos\' 1st child') || diag(dump($ast));
        isa_ok( $n[1][0][1],    QAST::IVal, :value(0),      '"positional" scoped VarWithFallback on rhs under bind ~> atpos\' 2nd child') || diag(dump($ast));
    }


    $ast := QAST::Stmts.new(    # `qumbl(|%xs<somekey> := @xs[0])`
        QAST::Op.new(:op<call>, :name('&qumbl'),
            QAST::Op.new(:op<bind>, :flat,
                QAST::VarWithFallback.new(:scope<associative>, :fallback(QAST::WVal.new(:value(NQPMu))),
                    QAST::Var.new(:name('%xs')),
                    QAST::SVal.new(:value<somekey>)
                ),
                QAST::VarWithFallback.new(:scope<positional>, :fallback(QAST::WVal.new(:value(NQPMu))),
                    QAST::Var.new(:name('@xs')),
                    QAST::IVal.new(:value(0))
                ),
            )
        )
    );
    #diag(dump($ast));
    replace_assoc_and_pos_scoped($ast);
    {
        my $n := $ast[0][0];
        isa_ok( $n,             QAST::SpecialArg, :named(NQPMu), :flat(1),  '"associative" VarWithFallback on lhs, "positional" on rhs under bind / bind stays SpecialArg if it was one') || diag(dump($ast));
        isa_ok( $n,             QAST::Op, :op<bindkey>,         '"associative" VarWithFallback on lhs, "positional" on rhs under bind / bind ~> Op bindkey') || diag(dump($ast));
        isa_ok( $n[0],          QAST::Var, :name('%xs'),        '"associative" VarWithFallback on lhs, "positional" on rhs under bind / lhs\' 1st child') || diag(dump($ast));
        isa_ok( $n[1],          QAST::SVal, :value<somekey>,    '"associative" VarWithFallback on lhs, "positional" on rhs under bind / lhs\' 2nd child') || diag(dump($ast));
        isa_ok( $n[2],          QAST::Op, :op<ifnull>,          '"associative" VarWithFallback on lhs, "positional" on rhs under bind / rhs ~> Op ifnull') || diag(dump($ast));
        isa_ok( $n[2][0],       QAST::Op, :op<atpos>,           '"associative" VarWithFallback on lhs, "positional" on rhs under bind / rhs ~> Op ifnull atpos ...') || diag(dump($ast));
        isa_ok( $n[2][1],       QAST::WVal, :value(NQPMu),      '"associative" VarWithFallback on lhs, "positional" on rhs under bind / rhs ~> Op ifnull ... WVal(NQPMu)') || diag(dump($ast));
        isa_ok( $n[2][0][0],    QAST::Var, :name('@xs'),        '"associative" VarWithFallback on lhs, "positional" on rhs under bind / atpos\' 1st child') || diag(dump($ast));
        isa_ok( $n[2][0][1],    QAST::IVal, :value(0),          '"associative" VarWithFallback on lhs, "positional" on rhs under bind / atpos\' 2nd child') || diag(dump($ast));
    }


    # check that non-trivial fallback is handled properly:
    #┬VarWithFallback associative :fallback((ifnull) ((atkey) ((who) (WVal GLOBALish)) (SVal "NO_VALUE")) (WVal NQPMu))
    #├─who
    #│ └○ $?PACKAGE
    #└◙ SVal "NO_VALUE"

    my $fallback := QAST::Op.new(:op<ifnull>,
        QAST::Op.new(:op<atkey>,
            QAST::Op.new(:op<who>,
                QAST::WVal.new(:value(GLOBALish)),
                QAST::SVal.new(:value<NO_VALUE>)
            )
        ),
        QAST::WVal.new(:value(NQPMu))
    );

    $ast := QAST::VarWithFallback.new(
        :scope<associative>,
        :$fallback,
        QAST::Op.new(:op<who>,
            QAST::Var.new(:name('$?PACKAGE'), :scope<lexical>)
        ),
        QAST::SVal.new(:value<NO_VALUE>)
    );
    #diag(dump($ast));
    $ast := replace_assoc_and_pos_scoped($ast);
    {
        isa_ok( $ast, QAST::Op, :op<ifnull>,    '"associative" VarWithFallback with complicated fallback ~> Op ifnull ...') || diag(dump($ast));
        isa_ok( $ast[0], QAST::Op, :op<atkey>,  '"associative" VarWithFallback with complicated fallback ~> Op ifnull atkey ...') || diag(dump($ast));
        is(     $ast[1], $fallback,             '"associative" VarWithFallback with complicated fallback ~> Op ifnull ... <fallback>') || diag(dump($ast));
        isa_ok( $ast[0][0], QAST::Op, :op<who>, '"associative" VarWithFallback with complicated fallback ~> atkey\'s 1st child ...') || diag(dump($ast));
        isa_ok( $ast[0][1], QAST::SVal, :value<NO_VALUE>,  '"associative" VarWithFallback with complicated fallback ~> atkey\'s 2nd child ...') || diag(dump($ast));
    }
    #diag(dump($ast));

    my $dummy0 := { # TODO: *IF* we could determine the type of preinc/predec (int, num, or bigint)
                    #       ...then we could translate VarWithFallBack under preinc/predec to the following:
        my $ast := QAST::Block.new(:blocktype<immediate>,
            QAST::Op.new(:op<bind>,
                QAST::Var.new(:name('%xs'), :scope<lexical>, :decl<var>),
                QAST::Op.new(:op<hash>,
                    QAST::SVal.new(:value<somekey>),
                    QAST::IVal.new(:value(7)),
                )
            ),
            QAST::Op.new(:op<add_i>,    # <<<<<< here's (1) were we need to know the type
                QAST::Op.new(:op<atkey>,
                    QAST::Var.new(:name('%xs'), :scope<lexical>),
                    QAST::SVal.new(:value<somekey>),
                ),
                QAST::IVal.new(:value(1))# <<<<<< here's (2) were we need to know the type
            ),
        );
        diag(dump($ast));
        my $code := nqp::getcomp('nqp').compile(:from('ast'), $ast);
        my $result := $code();
        diag($result);
    };

    for <preinc predec> -> $op {
        my $vwf := QAST::VarWithFallback.new(:scope<associative>, :fallback(WVal.new(:value(NQPMu))),
            QAST::Var.new(:name<%xs>),
            QAST::SVal.new(:value<somekey>)
        );
        my $ast := QAST::Op.new(:$op, $vwf);
        #diag(dump($ast));
        replace_assoc_and_pos_scoped($ast);
        #diag(dump($ast));
        is( $ast[0], $vwf, 'VarWithFallback "associative" under Op "' ~ $op ~ '" is untouched') || diag(dump($ast));
    }

    for <postinc postdec> -> $op {
        my $vwf := QAST::VarWithFallback.new(:scope<associative>, :fallback(WVal.new(:value(NQPMu))),
            QAST::Var.new(:name<%xs>),
            QAST::SVal.new(:value<somekey>)
        );
        my $ast := QAST::Op.new(:$op, $vwf);
        #diag(dump($ast));
        replace_assoc_and_pos_scoped($ast);
        #diag(dump($ast));

        is( $ast[0], $vwf, 'VarWithFallback "associative" under Op "' ~ $op ~ '" is untouched') || diag(dump($ast));
    }
}



{ # drop_takeclosure ----------------------------------------------------------
    my $ast;
    my $block1;
    my $block2;

    $ast := mkBlockWithCATCH();
    lives_ok({ drop_takeclosure($ast) }, 'drop_takeclosure can cope with exception handlers')
        || diag(dump($ast));


    $block1 := QAST::Block.new(
        QAST::Op.new(:op<iseq_s>,
            QAST::Var.new(:name('$x')),
            QAST::Var.new(:name('$name')),
        )
    );
    $block2 := QAST::Block.new(
        QAST::Var.new(:name('$x'), :decl<param>),
        QAST::Op.new(:op<takeclosure>,
            $block1
        )
    );
    $ast := QAST::Op.new(:op<bind>, # &fn := -> $x { -> { $x eq $name } }
        QAST::Var.new(:name('&fn')),
        QAST::Op.new(:op<takeclosure>,
            $block2
        )
    );
    #diag(dump($ast));
    $ast := drop_takeclosure($ast);
    #diag(dump($ast));

    ok( istype($ast, QAST::Op) && $ast.op eq 'bind', 'drop_takeclosure / sanity a)') || diag(dump($ast));
    is( nqp::elems($ast), 2, 'drop_takeclosure / sanity b: childcount)') || diag(dump($ast));
    ok( istype($ast[0], QAST::Var) && $ast[0].name eq '&fn', 'drop_takeclosure / sanity c)') || diag(dump($ast[0]));
    is( $ast[1], $block2, 'drop_takeclosure replaces outer Op takeclosure with its child block') || diag(dump($ast[1]));
    is( nqp::elems($ast[1]), 2, 'drop_takeclosure / sanity d: childcount of outer block)') || diag(dump($ast[1]));
    ok( istype($ast[1][0], QAST::Var) && $ast[1][0].name eq '$x', 'drop_takeclosure / sanity e)') || diag(dump($ast[1][0]));
    is( $ast[1][1], $block1, 'drop_takeclosure replaces inner Op takeclosure with its child block') || diag(dump($ast[1][1]));
    is( nqp::elems($ast[1][1]), 1, 'drop_takeclosure / sanity f: childcount of inner block)') || diag(dump($ast[1][1]));
    ok( istype($ast[1][1][0], QAST::Op) && $ast[1][1][0].op eq 'iseq_s', 'drop_takeclosure / sanity f)') || diag(dump($ast[1][1][0]));


    $block1 := QAST::Block.new(
        QAST::Var.new(:name('$x'), :decl<param>),
        QAST::Op.new(:op<iseq_s>,
            QAST::Var.new(:name('$x')),
            QAST::Var.new(:name('$name')),
        )
    );
    is( $ast[0].named, '', 'drop_takeclosure as named arg / sanity 0');
    $ast := QAST::Op.new(:op<call>, :name('&qumbl'),    # `qumbl(:fn(-> $x { $x eq $name }))`
        QAST::Op.new(:op<takeclosure>, :named<fn>,
            $block1
        )
    );
    #diag(dump($ast));
    $ast := drop_takeclosure($ast);
    #diag(dump($ast));

    ok( istype($ast, QAST::Op) && $ast.op eq 'call', 'drop_takeclosure as named arg / sanity a)') || diag(dump($ast));
    is( nqp::elems($ast), 1, 'drop_takeclosure as named arg / sanity b: child count of top node)') || diag(dump($ast));
    is( $ast[0], $block1, 'drop_takeclosure as named arg - replaces Op takeclosure with its child');
    is( $ast[0].named, 'fn', 'drop_takeclosure as named arg - copies .named attr if necessary');
}



done();
