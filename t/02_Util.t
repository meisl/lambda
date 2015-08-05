#!nqp
#^^^^ DON'T REMOVE OR CHANGE THIS FIRST LINE - NOR THIS ONE!!!
# Neither rename this file - the tests for linesFrom depend on it!
use testing;

use Util;

plan(185);


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


# - trim ----------------------------------------------------------------------

is(trim(''),        '',     'trim empty string');
is(trim(' '),       '',     'trim " "');
is(trim('  '),      '',     'trim "  "');
is(trim('x'),       'x',    'trim "x"');
is(trim('x '),      'x',    'trim "x "');
is(trim(' x'),      'x',    'trim " x"');
is(trim('x  '),     'x',    'trim "x  "');
is(trim(' x '),     'x',    'trim " x "');
is(trim('  x'),     'x',    'trim "  x"');
is(trim('xy'),      'xy',   'trim "xy"');
is(trim('xy  '),    'xy',   'trim "xy  "');
is(trim(' xy '),    'xy',   'trim " xy "');
is(trim('  xy'),    'xy',   'trim "  xy"');
is(trim('x y'),     'x y',  'trim "x y"');
is(trim('x y  '),   'x y',  'trim "x y  "');
is(trim(' x y '),   'x y',  'trim " x y "');
is(trim('  x y'),   'x y',  'trim "  x y"');


# - unixify -------------------------------------------------------------------

is(unixify('C:\rakudo\languages\nqp'), 'C:/rakudo/languages/nqp', 'unixify 1');
is(unixify('C:\rakudo/languages/nqp'), 'C:/rakudo/languages/nqp', 'unixify 2');

# - describe ------------------------------------------------------------------

is(describe(nqp::null), 'nqp::null', 'null is described as...');
is(describe(nqp::null_s), 'nqp::null_s (str)', 'null_s is described as...');

is(describe(QAST::Stmts), '(QAST::Stmts, Type object)', 'QAST::Stmts (type) is described as...');


is(describe(["foo", 1, ['hello', 'world'], 3.1415]), 
    '#`{NQPArray:}[ "foo" (str), 1 (int), #`{NQPArray:}[ "hello" (str), "world" (str) ], 3.1415 (num) ]',
    'describe(...)');

my $longstring := nqp::x('foobar', 100);
is(nqp::chars($longstring), 600, 'long str with 600 chars');
my $described := describe($longstring);
is(nqp::substr($described, 0, 7), '"foobar', 'str returned from describe starts with quoted prefix');
my $length := nqp::chars($described);
is(nqp::substr($described, $length - 13, 13), 'foobar" (str)', 'str returned from describe ends with quoted suffix');
ok($length < 600, 'str returned from describe is limited in length (< 600)');

my $block := QAST::Block.new;
is(describe($block), 'QAST::Block', 'a QAST::Block is described as...');
my $var := QAST::Var.new(:name<foo>, :scope<lexical>, :decl<var>);
is(describe($var), 'QAST::Var(lexical foo :decl(var))', 'a QAST::Var is described as...');
$block.push($var);
is(describe($block), 'QAST::Block', 'a QAST::Block is described without children');

# - join --------------------------------------------------------------------

is(join('#', ["a", "b", "c"]), 'a#b#c', 'basic join');
is(join('#', ["a", "b", "c"], :prefix1st), '#a#b#c', 'join with :prefix1st');
is(join('#', ["a", "b", "c"], :map(-> $x { $x ~ $x })), 'aa#bb#cc', 'join with :map');
is(join('|', [1, "b", 2]), '1 (int)|b|2 (int)', 'join uses describe as fallback for non-strings');
dies_ok( { nqp::join('|', [1, "b", 2]) }, '...wheras nqp::join dies when it encounters non-strings');

# - say -----------------------------------------------------------------------

my class FooBar {}
lives_ok( { say('# ', "b", 4711, nqp::null, nqp::null_s, FooBar) }, 'say can take any nr of args and uses describe when it encounters non-strings');

# - istype ------------------------------------------------------------------

dies_ok( { istype() }, 'istype with no arg');
dies_ok( { istype(nqp::null) }, 'istype with only one arg');


is(istype(NQPMu, nqp::null          ),  0, 'istype(NQPMu, nqp::null)');
is(istype(NQPMu, nqp::null_s        ),  0, 'istype(NQPMu, nqp::null_s)');
is(istype(NQPMu, NQPMu, nqp::null   ),  1, 'istype(NQPMu, NQPMu, nqp::null)');
is(istype(NQPMu, NQPMu, nqp::null_s ),  1, 'istype(NQPMu, NQPMu, nqp::null_s)');
is(istype(NQPMu, str                ),  0, 'istype(NQPMu, str)');
is(istype(NQPMu, int                ),  0, 'istype(NQPMu, int)');
is(istype(NQPMu, num                ),  0, 'istype(NQPMu, num)');

is(istype(nqp::null, NQPMu             ),   0, 'istype(nqp::null, NQPMu)');
is(istype(nqp::null, NQPMu, nqp::null  ),   1, 'istype(nqp::null, NQPMu, nqp::null)');
is(istype(nqp::null, NQPMu, nqp::null_s),   0, 'istype(nqp::null, NQPMu, nqp::null_s)');
is(istype(nqp::null, str               ),   0, 'istype(nqp::null, str)');
is(istype(nqp::null, int               ),   0, 'istype(nqp::null, int)');
is(istype(nqp::null, num               ),   0, 'istype(nqp::null, num)');

is(istype(nqp::null_s, NQPMu             ), 0, 'istype(nqp::null_s, NQPMu)');
is(istype(nqp::null_s, NQPMu, nqp::null  ), 0, 'istype(nqp::null_s, NQPMu, nqp::null)');
is(istype(nqp::null_s, NQPMu, nqp::null_s), 1, 'istype(nqp::null_s, NQPMu, nqp::null_s)');
is(istype(nqp::null_s, str               ), 1, 'istype(nqp::null_s, str)');
is(istype(nqp::null_s, int               ), 0, 'istype(nqp::null_s, int)');
is(istype(nqp::null_s, num               ), 0, 'istype(nqp::null_s, num)');

my class Foo {}
my class Bar is Foo {}
my role Baz {}
my $foo := Foo.new;
my $bar := Bar.new;
my $baz := Bar.new;
$baz.HOW.mixin($baz, Baz);


dies_ok( { istype(Foo) }, 'istype with only one arg');
dies_ok( { istype(Foo, $foo) }, 'istype with non-type arg as type (a)');
dies_ok( { istype(Foo, 'foo') }, 'istype with non-type arg as type (b)');

is(istype(Foo, NQPMu            ), 1, 'istype(Foo, NQPMu            )');
is(istype(Foo, NQPMu, nqp::null ), 1, 'istype(Foo, NQPMu, nqp::null )');
is(istype(Foo, NQPMu, Foo       ), 1, 'istype(Foo, NQPMu, Foo       )');
is(istype(Foo, Foo              ), 1, 'istype(Foo, Foo              )');
is(istype(Foo, Bar              ), 0, 'istype(Foo, Bar              )');
is(istype(Foo, Foo, Bar         ), 1, 'istype(Foo, Foo, Bar         )');
is(istype(Foo, Bar, Foo         ), 1, 'istype(Foo, Bar, Foo         )');
is(istype(Foo, Bar, Bar         ), 0, 'istype(Foo, Bar, Bar         )');

is(istype(Foo, Baz              ), 0, 'istype(Foo, Baz              )');
is(istype(Foo, Foo, Baz         ), 1, 'istype(Foo, Foo, Baz         )');
is(istype(Foo, Baz, Foo         ), 1, 'istype(Foo, Baz, Foo         )');
is(istype(Foo, Baz, Baz         ), 0, 'istype(Foo, Baz, Baz         )');


dies_ok( { istype($foo) }, 'istype with only one arg');
is(istype($foo, NQPMu           ), 1, 'istype(Foo.new, NQPMu           )');
is(istype($foo, NQPMu, nqp::null), 1, 'istype(Foo.new, NQPMu, nqp::null)');
is(istype($foo, NQPMu, Foo      ), 1, 'istype(Foo.new, NQPMu, Foo      )');
is(istype($foo, Foo             ), 1, 'istype(Foo.new, Foo             )');
is(istype($foo, Bar             ), 0, 'istype(Foo.new, Bar             )');
is(istype($foo, Foo, Bar        ), 1, 'istype(Foo.new, Foo, Bar        )');
is(istype($foo, Bar, Foo        ), 1, 'istype(Foo.new, Bar, Foo        )');
is(istype($foo, Bar, Bar        ), 0, 'istype(Foo.new, Bar, Bar        )');

is(istype($foo, Baz             ), 0, 'istype($foo, Baz            )');
is(istype($foo, Foo, Baz        ), 1, 'istype($foo, Foo, Baz       )');
is(istype($foo, Baz, Foo        ), 1, 'istype($foo, Baz, Foo       )');
is(istype($foo, Baz, Baz        ), 0, 'istype($foo, Baz, Baz       )');

is(istype($foo, str             ), 0, 'istype($foo, str)');
is(istype($foo, int             ), 0, 'istype($foo, int)');
is(istype($foo, num             ), 0, 'istype($foo, num)');


dies_ok( { istype(Bar) }, 'istype with only one arg');
is(istype(Bar, NQPMu            ), 1, 'istype(Bar, NQPMu           )');
is(istype(Bar, NQPMu, nqp::null ), 1, 'istype(Bar, NQPMu, nqp::null)');
is(istype(Bar, NQPMu, Foo       ), 1, 'istype(Bar, NQPMu, Foo      )');
is(istype(Bar, Foo              ), 1, 'istype(Bar, Foo             )');
is(istype(Bar, Bar              ), 1, 'istype(Bar, Bar             )');
is(istype(Bar, Foo, Bar         ), 1, 'istype(Bar, Foo, Bar        )');
is(istype(Bar, Bar, Foo         ), 1, 'istype(Bar, Bar, Foo        )');
is(istype(Bar, Bar, Bar         ), 1, 'istype(Bar, Bar, Bar        )');

is(istype(Bar, Baz              ), 0, 'istype(Bar, Baz             )');
is(istype(Bar, Foo, Baz         ), 1, 'istype(Bar, Foo, Baz        )');
is(istype(Bar, Baz, Foo         ), 1, 'istype(Bar, Baz, Foo        )');
is(istype(Bar, Baz, Baz         ), 0, 'istype(Bar, Baz, Baz        )');


dies_ok( { istype($bar) }, 'istype with only one arg');
is(istype($bar, NQPMu           ), 1, 'istype(Bar.new, NQPMu           )');
is(istype($bar, NQPMu, nqp::null), 1, 'istype(Bar.new, NQPMu, nqp::null)');
is(istype($bar, NQPMu, Foo      ), 1, 'istype(Bar.new, NQPMu, Foo      )');
is(istype($bar, Foo             ), 1, 'istype(Bar.new, Foo             )');
is(istype($bar, Bar             ), 1, 'istype(Bar.new, Bar             )');
is(istype($bar, Foo, Bar        ), 1, 'istype(Bar.new, Foo, Bar        )');
is(istype($bar, Bar, Foo        ), 1, 'istype(Bar.new, Bar, Foo        )');
is(istype($bar, Bar, Bar        ), 1, 'istype(Bar.new, Bar, Bar        )');

is(istype($bar, Baz             ), 0, 'istype($bar, Baz             )');
is(istype($bar, Foo, Baz        ), 1, 'istype($bar, Foo, Baz        )');
is(istype($bar, Baz, Foo        ), 1, 'istype($bar, Baz, Foo        )');
is(istype($bar, Baz, Baz        ), 0, 'istype($bar, Baz, Baz        )');


dies_ok( { istype($baz) }, 'istype with only one arg');
is(istype($baz, NQPMu           ), 1, 'istype(Bar.new does Baz, NQPMu           )');
is(istype($baz, NQPMu, nqp::null), 1, 'istype(Bar.new does Baz, NQPMu, nqp::null)');
is(istype($baz, NQPMu, Foo      ), 1, 'istype(Bar.new does Baz, NQPMu, Foo      )');
is(istype($baz, Foo             ), 1, 'istype(Bar.new does Baz, Foo             )');
is(istype($baz, Bar             ), 1, 'istype(Bar.new does Baz, Bar             )');
is(istype($baz, Foo, Bar        ), 1, 'istype(Bar.new does Baz, Foo, Bar        )');
is(istype($baz, Bar, Foo        ), 1, 'istype(Bar.new does Baz, Bar, Foo        )');
is(istype($baz, Bar, Bar        ), 1, 'istype(Bar.new does Baz, Bar, Bar        )');

is(istype($baz, Baz             ), 1, 'istype($baz, Baz             )');
is(istype($baz, Foo, Baz        ), 1, 'istype($baz, Foo, Baz        )');
is(istype($baz, Baz, Foo        ), 1, 'istype($baz, Baz, Foo        )');
is(istype($baz, Baz, Baz        ), 1, 'istype($baz, Baz, Baz        )');


is(istype("foo", nqp::null_s),  0, 'istype("foo", nqp::null_s)');
is(istype("foo", nqp::null),    0, 'istype("foo", nqp::null)');
is(istype("foo", str),          1, 'istype("foo", str)');
is(istype("foo", int),          0, 'istype("foo", int)');
is(istype("foo", num),          0, 'istype("foo", num)');

is(istype(str, nqp::null_s),    0, 'istype(str, nqp::null_s)');
is(istype(str, nqp::null),      0, 'istype(str, nqp::null)');
is(istype(str, str),            1, 'istype(str, str)');
is(istype(str, int),            0, 'istype(str, int)');
is(istype(str, num),            0, 'istype(str, num)');

is(istype(nqp::null_s, nqp::null_s),    1, 'istype(str, nqp::null_s)');
is(istype(nqp::null_s, nqp::null),      0, 'istype(nqp::null_s, nqp::null)');
is(istype(nqp::null_s, str),            1, 'istype(nqp::null_s, str)');
is(istype(nqp::null_s, int),            0, 'istype(nqp::null_s, int)');
is(istype(nqp::null_s, num),            0, 'istype(nqp::null_s, num)');


is(istype(4711, nqp::null_s),   0, 'istype(4711, nqp::null_s)');
is(istype(4711, nqp::null),     0, 'istype(4711, nqp::null)');
is(istype(4711, str),           0, 'istype(4711, str)');
is(istype(4711, int),           1, 'istype(4711, int)');
is(istype(4711, num),           0, 'istype(4711, num)');

is(istype(int, nqp::null_s),    0, 'istype(int, nqp::null_s)');
is(istype(int, nqp::null),      0, 'istype(int, nqp::null)');
is(istype(int, str),            0, 'istype(int, str)');
is(istype(int, int),            1, 'istype(int, int)');
is(istype(int, num),            0, 'istype(int, num)');


is(istype(3.14, nqp::null_s),   0, 'istype(3.14, nqp::null_s)');
is(istype(3.14, nqp::null),     0, 'istype(3.14, nqp::null)');
is(istype(3.14, str),           0, 'istype(3.14, str)');
is(istype(3.14, int),           0, 'istype(3.14, int)');
is(istype(3.14, num),           1, 'istype(3.14, num)');

is(istype(num, nqp::null_s),    0, 'istype(num, nqp::null_s)');
is(istype(num, nqp::null),      0, 'istype(num, nqp::null)');
is(istype(num, str),            0, 'istype(num, str)');
is(istype(num, int),            0, 'istype(num, int)');
is(istype(num, num),            1, 'istype(num, num)');


# - linesFrom -----------------------------------------------------------------

my @lines;
lives_ok( { @lines := linesFrom('t/02_Util.t', 1) }, 'linesFrom this test file, all');
is(@lines[0], "#!nqp\n", , 'linesFrom this test file, 1st');

lives_ok( { @lines := linesFrom('t/02_Util.t', 2, 1) }, 'linesFrom this test file, only 2nd');
is(nqp::elems(@lines), 1, 'nr of strings returned from linesFrom(..., 2, 1)')
    || diag(' got: ' ~ describe(@lines));
is(@lines[0], "#^^^^ DON'T REMOVE OR CHANGE THIS FIRST LINE - NOR THIS ONE!!!\n", , 'linesFrom this test file, 2nd');


done();
