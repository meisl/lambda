#!nqp
#^^^^ DON'T REMOVE OR CHANGE THIS FIRST LINE - NOR THIS ONE!!!
use testing;

use Util;

plan(92);


is(max(  -1,    0),    0, 'max(  -1,    0)');
is(max(   0,   -1),    0, 'max(   0,   -1)');
is(max(   0,    0),    0, 'max(   0,    0)');
is(max(   0,    1),    1, 'max(   0,    1)');
is(max(   1,    0),    1, 'max(   1,    0)');
is(max(4711, 4710), 4711, 'max(4711, 4710)');
is(min(4711, 4711), 4711, 'min(4711, 4711)');
is(max( -23,   42),   42, 'max( -23,   42)');
is(max(  42,  -23),   42, 'max(  42,  -23)');


is(min(  -1,    0),   -1, 'min(  -1,    0)');
is(min(   0,   -1),   -1, 'min(   0,   -1)');
is(min(   0,    0),    0, 'min(   0,    0)');
is(min(   0,    1),    0, 'min(   0,    1)');
is(min(   1,    0),    0, 'min(   1,    0)');
is(min(4711, 4710), 4710, 'min(4711, 4710)');
is(min(4711, 4711), 4711, 'min(4711, 4711)');
is(min( -23,   42),  -23, 'min( -23,   42)');
is(min(  42,  -23),  -23, 'min(  42,  -23)');


is(whatsit(["foo", 1, ['hello', 'world'], 3.1415]), 
    "[\"foo\", P6int 1, [\"hello\", \"world\"], P6num 3.1415]", 'whatsit(...)');


is(istypeAny(nqp::null                  ), 0, 'istypeAny(nqp::null                  )');
is(istypeAny(nqp::null, NQPMu           ), 0, 'istypeAny(nqp::null, NQPMu           )');
is(istypeAny(nqp::null, NQPMu, nqp::null), 0, 'istypeAny(nqp::null, NQPMu, nqp::null)');

my class Foo {}
my class Bar is Foo {}
my role Baz {}
my $foo := Foo.new;
my $bar := Bar.new;
my $baz := Bar.new;
$baz.HOW.mixin($baz, Baz);

is(istypeAny(Foo                   ), 0, 'istypeAny(Foo                   )');
is(istypeAny(Foo, NQPMu            ), 1, 'istypeAny(Foo, NQPMu            )');
is(istypeAny(Foo, NQPMu, nqp::null ), 1, 'istypeAny(Foo, NQPMu, nqp::null )');
is(istypeAny(Foo, NQPMu, Foo       ), 1, 'istypeAny(Foo, NQPMu, Foo       )');
is(istypeAny(Foo, Foo              ), 1, 'istypeAny(Foo, Foo              )');
is(istypeAny(Foo, Bar              ), 0, 'istypeAny(Foo, Bar              )');
is(istypeAny(Foo, Foo, Bar         ), 1, 'istypeAny(Foo, Foo, Bar         )');
is(istypeAny(Foo, Bar, Foo         ), 1, 'istypeAny(Foo, Bar, Foo         )');
is(istypeAny(Foo, Bar, Bar         ), 0, 'istypeAny(Foo, Bar, Bar         )');

is(istypeAny(Foo, Baz              ), 0, 'istypeAny(Foo, Baz              )');
is(istypeAny(Foo, Foo, Baz         ), 1, 'istypeAny(Foo, Foo, Baz         )');
is(istypeAny(Foo, Baz, Foo         ), 1, 'istypeAny(Foo, Baz, Foo         )');
is(istypeAny(Foo, Baz, Baz         ), 0, 'istypeAny(Foo, Baz, Baz         )');


is(istypeAny($foo                  ), 0, 'istypeAny(Foo.new                  )');
is(istypeAny($foo, NQPMu           ), 1, 'istypeAny(Foo.new, NQPMu           )');
is(istypeAny($foo, NQPMu, nqp::null), 1, 'istypeAny(Foo.new, NQPMu, nqp::null)');
is(istypeAny($foo, NQPMu, Foo      ), 1, 'istypeAny(Foo.new, NQPMu, Foo      )');
is(istypeAny($foo, Foo             ), 1, 'istypeAny(Foo.new, Foo             )');
is(istypeAny($foo, Bar             ), 0, 'istypeAny(Foo.new, Bar             )');
is(istypeAny($foo, Foo, Bar        ), 1, 'istypeAny(Foo.new, Foo, Bar        )');
is(istypeAny($foo, Bar, Foo        ), 1, 'istypeAny(Foo.new, Bar, Foo        )');
is(istypeAny($foo, Bar, Bar        ), 0, 'istypeAny(Foo.new, Bar, Bar        )');

is(istypeAny($foo, Baz             ), 0, 'istypeAny($foo, Baz            )');
is(istypeAny($foo, Foo, Baz        ), 1, 'istypeAny($foo, Foo, Baz       )');
is(istypeAny($foo, Baz, Foo        ), 1, 'istypeAny($foo, Baz, Foo       )');
is(istypeAny($foo, Baz, Baz        ), 0, 'istypeAny($foo, Baz, Baz       )');


is(istypeAny(Bar                   ), 0, 'istypeAny(Bar                  )');
is(istypeAny(Bar, NQPMu            ), 1, 'istypeAny(Bar, NQPMu           )');
is(istypeAny(Bar, NQPMu, nqp::null ), 1, 'istypeAny(Bar, NQPMu, nqp::null)');
is(istypeAny(Bar, NQPMu, Foo       ), 1, 'istypeAny(Bar, NQPMu, Foo      )');
is(istypeAny(Bar, Foo              ), 1, 'istypeAny(Bar, Foo             )');
is(istypeAny(Bar, Bar              ), 1, 'istypeAny(Bar, Bar             )');
is(istypeAny(Bar, Foo, Bar         ), 1, 'istypeAny(Bar, Foo, Bar        )');
is(istypeAny(Bar, Bar, Foo         ), 1, 'istypeAny(Bar, Bar, Foo        )');
is(istypeAny(Bar, Bar, Bar         ), 1, 'istypeAny(Bar, Bar, Bar        )');

is(istypeAny(Bar, Baz              ), 0, 'istypeAny(Bar, Baz             )');
is(istypeAny(Bar, Foo, Baz         ), 1, 'istypeAny(Bar, Foo, Baz        )');
is(istypeAny(Bar, Baz, Foo         ), 1, 'istypeAny(Bar, Baz, Foo        )');
is(istypeAny(Bar, Baz, Baz         ), 0, 'istypeAny(Bar, Baz, Baz        )');


is(istypeAny($bar                  ), 0, 'istypeAny(Bar.new                  )');
is(istypeAny($bar, NQPMu           ), 1, 'istypeAny(Bar.new, NQPMu           )');
is(istypeAny($bar, NQPMu, nqp::null), 1, 'istypeAny(Bar.new, NQPMu, nqp::null)');
is(istypeAny($bar, NQPMu, Foo      ), 1, 'istypeAny(Bar.new, NQPMu, Foo      )');
is(istypeAny($bar, Foo             ), 1, 'istypeAny(Bar.new, Foo             )');
is(istypeAny($bar, Bar             ), 1, 'istypeAny(Bar.new, Bar             )');
is(istypeAny($bar, Foo, Bar        ), 1, 'istypeAny(Bar.new, Foo, Bar        )');
is(istypeAny($bar, Bar, Foo        ), 1, 'istypeAny(Bar.new, Bar, Foo        )');
is(istypeAny($bar, Bar, Bar        ), 1, 'istypeAny(Bar.new, Bar, Bar        )');

is(istypeAny($bar, Baz             ), 0, 'istypeAny($bar, Baz             )');
is(istypeAny($bar, Foo, Baz        ), 1, 'istypeAny($bar, Foo, Baz        )');
is(istypeAny($bar, Baz, Foo        ), 1, 'istypeAny($bar, Baz, Foo        )');
is(istypeAny($bar, Baz, Baz        ), 0, 'istypeAny($bar, Baz, Baz        )');


is(istypeAny($baz                  ), 0, 'istypeAny(Bar.new does Baz                  )');
is(istypeAny($baz, NQPMu           ), 1, 'istypeAny(Bar.new does Baz, NQPMu           )');
is(istypeAny($baz, NQPMu, nqp::null), 1, 'istypeAny(Bar.new does Baz, NQPMu, nqp::null)');
is(istypeAny($baz, NQPMu, Foo      ), 1, 'istypeAny(Bar.new does Baz, NQPMu, Foo      )');
is(istypeAny($baz, Foo             ), 1, 'istypeAny(Bar.new does Baz, Foo             )');
is(istypeAny($baz, Bar             ), 1, 'istypeAny(Bar.new does Baz, Bar             )');
is(istypeAny($baz, Foo, Bar        ), 1, 'istypeAny(Bar.new does Baz, Foo, Bar        )');
is(istypeAny($baz, Bar, Foo        ), 1, 'istypeAny(Bar.new does Baz, Bar, Foo        )');
is(istypeAny($baz, Bar, Bar        ), 1, 'istypeAny(Bar.new does Baz, Bar, Bar        )');

is(istypeAny($baz, Baz             ), 1, 'istypeAny($baz, Baz             )');
is(istypeAny($baz, Foo, Baz        ), 1, 'istypeAny($baz, Foo, Baz        )');
is(istypeAny($baz, Baz, Foo        ), 1, 'istypeAny($baz, Baz, Foo        )');
is(istypeAny($baz, Baz, Baz        ), 1, 'istypeAny($baz, Baz, Baz        )');

my @lines;
lives_ok( { @lines := linesFrom('t/02_Util.t', 1) }, 'linesFrom this test file, all');
is(@lines[0], "#!nqp\n", , 'linesFrom this test file, 1st');

lives_ok( { @lines := linesFrom('t/02_Util.t', 2, 1) }, 'linesFrom this test file, only 2nd');
is(nqp::elems(@lines), 1, 'nr of strings returned from linesFrom(..., 2, 1)')
    || diag(' got: ' ~ whatsit(@lines));
is(@lines[0], "#^^^^ DON'T REMOVE OR CHANGE THIS FIRST LINE - NOR THIS ONE!!!\n", , 'linesFrom this test file, 2nd');

