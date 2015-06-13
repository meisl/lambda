#!nqp

use testing;
use Util::TreeWalk;

plan(36);


my $do1 := TreeWalkDo.recurse(:take);
my $do1s := 'TreeWalkDo.recurse(:take)';
diag($do1.nqp);

is($do1.take,    1, "$do1s.take");
is($do1.recurse, 1, "$do1s.recurse");
is($do1.return , 0, "$do1s.return");
is($do1.last ,   0, "$do1s.last");
is($do1.break ,  0, "$do1s.break");
is($do1.halt ,   0, "$do1s.halt");


my $do2 := $do1.recurse(:take(!$do1.take));
my $do2s := '$do1.recurse(:take(!$do1.take))';
diag($do2.nqp);

is($do2.take,    0, "$do2s.take");
is($do2.recurse, 1, "$do2s.recurse");
is($do2.return , 0, "$do2s.return");
is($do2.last ,   0, "$do2s.last");
is($do2.break ,  0, "$do2s.break");
is($do2.halt ,   0, "$do2s.halt");


my $do3 := $do1.return(:take(!$do1.take));
my $do3s := '$do1.return(:take(!$do1.take))';
diag($do3.nqp);

is($do3.take,    0, "$do3s.take");
is($do3.recurse, 0, "$do3s.recurse");
is($do3.return , 1, "$do3s.return");
is($do3.last ,   0, "$do3s.last");
is($do3.break ,  0, "$do3s.break");
is($do3.halt ,   0, "$do3s.halt");


my $do4 := $do1.last(:!take);
my $do4s := '$do1.last(:!take)';
diag($do4.nqp);

is($do4.take,    0, "$do4s.take");
is($do4.recurse, 0, "$do4s.recurse");
is($do4.return , 0, "$do4s.return");
is($do4.last ,   1, "$do4s.last");
is($do4.break ,  0, "$do4s.break");
is($do4.halt ,   0, "$do4s.halt");


my $do5 := $do1.break(:take);
my $do5s := '$do1.break(:take)';
diag($do5.nqp);

is($do5.take,    1, "$do5s.take");
is($do5.recurse, 0, "$do5s.recurse");
is($do5.return , 0, "$do5s.return");
is($do5.last ,   0, "$do5s.last");
is($do5.break ,  1, "$do5s.break");
is($do5.halt ,   0, "$do5s.halt");


my $do6 := $do1.halt(:take);
my $do6s := '$do1.halt(:take)';
diag($do6.nqp);

is($do6.take,    1, "$do6s.take");
is($do6.recurse, 0, "$do6s.recurse");
is($do6.return , 0, "$do6s.return");
is($do6.last ,   0, "$do6s.last");
is($do6.break ,  0, "$do6s.break");
is($do6.halt ,   1, "$do6s.halt");


done();
