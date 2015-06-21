#!nqp
use QAST;   # that is, nqp's

use testing;
use Util;

use Util::QAST;

plan(74);


my $w := QAST::WVal.new(:value(NQPMu));
is(dump($w), '─◙ WVal NQPMu', 'dump world value NQPMu');

my $vwf := QAST::VarWithFallback.new(:scope<positional>, :fallback(QAST::WVal.new(:value(NQPMu))), :decl(nqp::null_s));
is(dump($vwf), '─○┬VarWithFallback positional :fallback(WVal NQPMu)', 'dump VarWithFallback');
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

my $ast := QAST::CompUnit.new(
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

    my $stmts_topmost := QAST::Stmts.new(
        QAST::Block.new(
            QAST::Var.new(:name<$x>, :decl<param>),
            QAST::Op.new(:op<say>,
                $stmts_needed
            ),
        )
    );
    my $ast := $stmts_topmost;

    diag('check :resultChild fixup in ' ~ $STMT_KIND.HOW.name($STMT_KIND) ~ "\n" ~ dump($ast));

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

    is(resultterm($stmts_inner), $resultVar, 'result term of the inner Stmts')
        || diag(dump($stmts_inner));
    is(resultterm($stmts_needed), $stmts_inner, 'result term of the outer Stmts')
        || diag(dump($stmts_needed));

    $ast := drop_Stmts($ast);

    is($ast, $stmts_topmost, 'topmost Stmts is not dropped');

    is($ast[0][1][0], $stmts_needed, 'Stmts under `say` is not dropped')
        || diag(dump($ast));
    is(resultterm($stmts_needed), $resultVar, 'either :resultchild is set to correct value or deleted')
        || diag(dump($ast));
    is($stmts_needed[0], $stmt, 'Stmt (singular!) nodes are not dropped')
        || diag(dump($ast));

    #diag(dump($ast));
}


{
    # {
    #   nqp::die('BOOM!');
    #   CATCH {
    #       nqp::say($!);
    #   }
    # }

    # ...gets compiled to:

    my $ast := QAST::Op.new(:op<handle>,
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

}

{ # replace_assoc_and_pos_scoped ----------------------------------------------
    my $ast;
    
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
    ok( istype($ast[0][0], QAST::Op) && $ast[0][0].op eq 'atpos', '"positional" scoped VarWithFallback is replaced by Op atpos')
        || diag(describe($ast[0][0]));
    ok( !istype($ast[0][0], QAST::SpecialArg), 'filled in Op should not be SpecialArg when original wasn\'t one')
        || diag(describe($ast[0][0]));

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
    ok( istype($ast[0][0], QAST::Op) && $ast[0][0].op eq 'atkey', '"associative" scoped VarWithFallback is replaced by Op atpos')
        || diag(describe($ast[0][0]));
    ok( !istype($ast[0][0], QAST::SpecialArg), 'filled in Op should not be SpecialArg when original wasn\'t one')
        || diag(describe($ast[0][0]));
}


done();
