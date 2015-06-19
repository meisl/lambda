#!nqp

use testing;
use Util::QAST;

use Util::TreeWalk;

plan(186);



# TreeWalkDo.XYZ --------------------------------------------------------------


my $do1 := TreeWalkDo.recurse(:take);
my $do1s := 'TreeWalkDo.recurse(:take)';
diag($do1.nqp);

is($do1.take,    1, "$do1.take");
is($do1.recurse, 1, "$do1.recurse");
is($do1.return , 0, "$do1.return");
is($do1.last ,   0, "$do1.last");
is($do1.break ,  0, "$do1.break");
is($do1.halt ,   0, "$do1.halt");


my $do2 := $do1.recurse(:take(!$do1.take));
my $do2s := '$do1.recurse(:take(!$do1.take))';
diag($do2.nqp);

is($do2.take,    0, "$do2.take");
is($do2.recurse, 1, "$do2.recurse");
is($do2.return , 0, "$do2.return");
is($do2.last ,   0, "$do2.last");
is($do2.break ,  0, "$do2.break");
is($do2.halt ,   0, "$do2.halt");


my $do3 := $do1.return(:take(!$do1.take));
my $do3s := '$do1.return(:take(!$do1.take))';
diag($do3.nqp);

is($do3.take,    0, "$do3.take");
is($do3.recurse, 0, "$do3.recurse");
is($do3.return , 1, "$do3.return");
is($do3.last ,   0, "$do3.last");
is($do3.break ,  0, "$do3.break");
is($do3.halt ,   0, "$do3.halt");


my $do4 := $do1.last(:!take);
my $do4s := '$do1.last(:!take)';
diag($do4.nqp);

is($do4.take,    0, "$do4.take");
is($do4.recurse, 0, "$do4.recurse");
is($do4.return , 0, "$do4.return");
is($do4.last ,   1, "$do4.last");
is($do4.break ,  0, "$do4.break");
is($do4.halt ,   0, "$do4.halt");


my $do5 := $do1.break(:take);
my $do5s := '$do1.break(:take)';
diag($do5.nqp);

is($do5.take,    1, "$do5.take");
is($do5.recurse, 0, "$do5.recurse");
is($do5.return , 0, "$do5.return");
is($do5.last ,   0, "$do5.last");
is($do5.break ,  1, "$do5.break");
is($do5.halt ,   0, "$do5.halt");


my $do6 := $do1.halt(:take);
my $do6s := '$do1.halt(:take)';
diag($do6.nqp);

is($do6.take,    1, "$do6.take");
is($do6.recurse, 0, "$do6.recurse");
is($do6.return , 0, "$do6.return");
is($do6.last ,   0, "$do6.last");
is($do6.break ,  0, "$do6.break");
is($do6.halt ,   1, "$do6.halt");



# TreeWalk.dfs-up -------------------------------------------------------------

my $tree1 := [1, [2, 3], 4];

my @pcalls := [];
my &probe := -> $node, @pathUp {
    @pcalls.push([$node, nqp::clone(@pathUp)]);
    TreeWalkDo.recurse(:take(nqp::isint($node)));
};

my @ccalls := [];
my &consumer := -> $node, @pathUp {
    @ccalls.push([$node, nqp::clone(@pathUp)]);
};


dies_ok({ TreeWalk.dfs-up(&probe, &consumer, $tree1, []) }, 'TreeWalk.dfs-up, when given an additional array arg,');

my $out := TreeWalk.dfs-up(&probe, &consumer, $tree1);

is($out, $tree1, 'TreeWalk.dfs-up returns the tree that it received');


is(nqp::elems(@pcalls), 6, 'nr of calls to &probe')
    || diag(@pcalls);
is(nqp::elems(@ccalls), 4, 'nr of calls to &consumer')
    || diag(@ccalls);

# calls to &probe
is(           @pcalls[0][0],    $tree1,         'probe call 1 arg node');
is(nqp::elems(@pcalls[0][1]),   0,              'probe call 1 arg pathUp length');

is(           @pcalls[1][0],    $tree1[0],      'probe call 2 arg node');
is(nqp::elems(@pcalls[1][1]),   1,              'probe call 2 arg pathUp length');
is(           @pcalls[1][1][0], $tree1,         'probe call 2 arg pathUp[0]');

is(           @pcalls[2][0],    $tree1[1],      'probe call 3 arg node');
is(nqp::elems(@pcalls[2][1]),   1,              'probe call 3 arg pathUp length');
is(           @pcalls[2][1][0], $tree1,         'probe call 3 arg pathUp[0]');

is(           @pcalls[3][0],    $tree1[1][0],   'probe call 4 arg node');
is(nqp::elems(@pcalls[3][1]),   2,              'probe call 4 arg pathUp length');
is(           @pcalls[3][1][0], $tree1[1],      'probe call 4 arg pathUp[0]');
is(           @pcalls[3][1][1], $tree1,         'probe call 4 arg pathUp[1]');

is(           @pcalls[4][0],    $tree1[1][1],   'probe call 5 arg node');
is(nqp::elems(@pcalls[4][1]),   2,              'probe call 5 arg pathUp length');
is(           @pcalls[4][1][0], $tree1[1],      'probe call 5 arg pathUp[0]');
is(           @pcalls[4][1][1], $tree1,         'probe call 5 arg pathUp[1]');

is(           @pcalls[5][0],    $tree1[2],      'probe call 6 arg node');
is(nqp::elems(@pcalls[5][1]),   1,              'probe call 6 arg pathUp length');
is(           @pcalls[5][1][0], $tree1,         'probe call 6 arg pathUp[0]');

# calls to &consumer
is(           @ccalls[0][0],    $tree1[0],      'consumer call 1 arg node');
is(nqp::elems(@ccalls[0][1]),   1,              'consumer call 1 arg pathUp length');
is(           @ccalls[0][1][0], $tree1,         'consumer call 1 arg pathUp[0]');

is(           @ccalls[1][0],    $tree1[1][0],   'consumer call 2 arg node');
is(nqp::elems(@ccalls[1][1]),   2,              'consumer call 2 arg pathUp length');
is(           @ccalls[1][1][0], $tree1[1],      'consumer call 2 arg pathUp[0]');
is(           @ccalls[1][1][1], $tree1,         'consumer call 2 arg pathUp[1]');

is(           @ccalls[2][0],    $tree1[1][1],   'consumer call 3 arg node');
is(nqp::elems(@ccalls[2][1]),   2,              'consumer call 3 arg pathUp length');
is(           @ccalls[2][1][0], $tree1[1],      'consumer call 3 arg pathUp[0]');
is(           @ccalls[2][1][1], $tree1,         'consumer call 3 arg pathUp[1]');

is(           @ccalls[3][0],    $tree1[2],      'consumer call 4 arg node');
is(nqp::elems(@ccalls[3][1]),   1,              'consumer call 4 arg pathUp length');
is(           @ccalls[3][1][0], $tree1,         'consumer call 4 arg pathUp[0]');

# -----------------------------------------------------------------------

@pcalls := [];
@ccalls := [];
&probe := -> $node, @pathUp {
    @pcalls.push([$node, nqp::clone(@pathUp)]);
    if 0 == +@pathUp {
        TreeWalkDo.recurse(:!take);
    } else {
        TreeWalkDo.return(:take);
    }
};

TreeWalk.dfs-up(&probe, &consumer, $tree1);

is(nqp::elems(@pcalls), 4, 'nr of calls to &probe')
    || diag(@pcalls);
is(nqp::elems(@ccalls), 3, 'nr of calls to &consumer')
    || diag(@ccalls);

# calls to &probe
is(           @pcalls[0][0],    $tree1,         'probe call 1 arg node');
is(nqp::elems(@pcalls[0][1]),   0,              'probe call 1 arg pathUp length');

is(           @pcalls[1][0],    $tree1[0],      'probe call 2 arg node');
is(nqp::elems(@pcalls[1][1]),   1,              'probe call 2 arg pathUp length');
is(           @pcalls[1][1][0], $tree1,         'probe call 2 arg pathUp[0]');

is(           @pcalls[2][0],    $tree1[1],      'probe call 3 arg node');
is(nqp::elems(@pcalls[2][1]),   1,              'probe call 3 arg pathUp length');
is(           @pcalls[2][1][0], $tree1,         'probe call 3 arg pathUp[0]');

is(           @pcalls[3][0],    $tree1[2],      'probe call 4 arg node');
is(nqp::elems(@pcalls[3][1]),   1,              'probe call 4 arg pathUp length');
is(           @pcalls[3][1][0], $tree1,         'probe call 4 arg pathUp[0]');

# calls to &consumer
is(           @ccalls[0][0],    $tree1[0],      'consumer call 1 arg node');
is(nqp::elems(@ccalls[0][1]),   1,              'consumer call 1 arg pathUp length');
is(           @ccalls[0][1][0], $tree1,         'consumer call 1 arg pathUp[0]');

is(           @ccalls[1][0],    $tree1[1],      'consumer call 2 arg node');
is(nqp::elems(@ccalls[1][1]),   1,              'consumer call 2 arg pathUp length');
is(           @ccalls[1][1][0], $tree1,         'consumer call 2 arg pathUp[0]');

is(           @ccalls[2][0],    $tree1[2],      'consumer call 3 arg node');
is(nqp::elems(@ccalls[2][1]),   1,              'consumer call 3 arg pathUp length');
is(           @ccalls[2][1][0], $tree1,         'consumer call 3 arg pathUp[0]');

# -----------------------------------------------------------------------

@pcalls := [];
@ccalls := [];
&probe := -> $node, @pathUp {
    @pcalls.push([$node, nqp::clone(@pathUp)]);
    if +@pathUp < 2 {
        TreeWalkDo.recurse(:take(!!@pathUp));
    } else {
        TreeWalkDo.last(:take);
    }
};

TreeWalk.dfs-up(&probe, &consumer, $tree1);

is(nqp::elems(@pcalls), 5, 'nr of calls to &probe')
    || diag(@pcalls);
is(nqp::elems(@ccalls), 4, 'nr of calls to &consumer')
    || diag(@ccalls);

# calls to &probe
is(           @pcalls[0][0],    $tree1,         'probe call 1 arg node');
is(nqp::elems(@pcalls[0][1]),   0,              'probe call 1 arg pathUp length');

is(           @pcalls[1][0],    $tree1[0],      'probe call 2 arg node');
is(nqp::elems(@pcalls[1][1]),   1,              'probe call 2 arg pathUp length');
is(           @pcalls[1][1][0], $tree1,         'probe call 2 arg pathUp[0]');

is(           @pcalls[2][0],    $tree1[1],      'probe call 3 arg node');
is(nqp::elems(@pcalls[2][1]),   1,              'probe call 3 arg pathUp length');
is(           @pcalls[2][1][0], $tree1,         'probe call 3 arg pathUp[0]');

is(           @pcalls[3][0],    $tree1[1][0],   'probe call 4 arg node');
is(nqp::elems(@pcalls[3][1]),   2,              'probe call 4 arg pathUp length');
is(           @pcalls[3][1][0], $tree1[1],      'probe call 4 arg pathUp[0]');
is(           @pcalls[3][1][1], $tree1,         'probe call 4 arg pathUp[1]');

is(           @pcalls[4][0],    $tree1[2],      'probe call 5 arg node');
is(nqp::elems(@pcalls[4][1]),   1,              'probe call 5 arg pathUp length');
is(           @pcalls[4][1][0], $tree1,         'probe call 5 arg pathUp[0]');

# calls to &consumer
is(           @ccalls[0][0],    $tree1[0],      'consumer call 1 arg node');
is(nqp::elems(@ccalls[0][1]),   1,              'consumer call 1 arg pathUp length');
is(           @ccalls[0][1][0], $tree1,         'consumer call 1 arg pathUp[0]');

# note: it's dfs-*UP*
is(           @ccalls[1][0],    $tree1[1][0],   'consumer call 2 arg node');
is(nqp::elems(@ccalls[1][1]),   2,              'consumer call 2 arg pathUp length');
is(           @ccalls[1][1][0], $tree1[1],      'consumer call 2 arg pathUp[0]');
is(           @ccalls[1][1][1], $tree1,         'consumer call 2 arg pathUp[1]');

is(           @ccalls[2][0],    $tree1[1],      'consumer call 3 arg node');
is(nqp::elems(@ccalls[2][1]),   1,              'consumer call 3 arg pathUp length');
is(           @ccalls[2][1][0], $tree1,         'consumer call 3 arg pathUp[0]');

is(           @ccalls[3][0],    $tree1[2],      'consumer call 4 arg node');
is(nqp::elems(@ccalls[3][1]),   1,              'consumer call 4 arg pathUp length');
is(           @ccalls[3][1][0], $tree1,         'consumer call 4 arg pathUp[0]');

# -----------------------------------------------------------------------

@pcalls := [];
@ccalls := [];
&probe := -> $node, @pathUp {
    @pcalls.push([$node, nqp::clone(@pathUp)]);
    if $node =:= $tree1 {
        TreeWalkDo.recurse(:!take);
    } else {
        if (nqp::isint($node)) {
            TreeWalkDo.return(:take);
        } else {
            TreeWalkDo.last(:take);
        }
    }
};

TreeWalk.dfs-up(&probe, &consumer, $tree1);

is(nqp::elems(@pcalls), 3, 'nr of calls to &probe')
    || diag(@pcalls);
is(nqp::elems(@ccalls), 2, 'nr of calls to &consumer')
    || diag(@ccalls);

# calls to &probe
is(           @pcalls[0][0],    $tree1,         'probe call 1 arg node');
is(nqp::elems(@pcalls[0][1]),   0,              'probe call 1 arg pathUp length');

is(           @pcalls[1][0],    $tree1[0],      'probe call 2 arg node');
is(nqp::elems(@pcalls[1][1]),   1,              'probe call 2 arg pathUp length');
is(           @pcalls[1][1][0], $tree1,         'probe call 2 arg pathUp[0]');

is(           @pcalls[2][0],    $tree1[1],      'probe call 3 arg node');
is(nqp::elems(@pcalls[2][1]),   1,              'probe call 3 arg pathUp length');
is(           @pcalls[2][1][0], $tree1,         'probe call 3 arg pathUp[0]');

# calls to &consumer
is(           @ccalls[0][0],    $tree1[0],      'consumer call 1 arg node');
is(nqp::elems(@ccalls[0][1]),   1,              'consumer call 1 arg pathUp length');
is(           @ccalls[0][1][0], $tree1,         'consumer call 1 arg pathUp[0]');

is(           @ccalls[1][0],    $tree1[1],      'consumer call 2 arg node');
is(nqp::elems(@ccalls[1][1]),   1,              'consumer call 2 arg pathUp length');
is(           @ccalls[1][1][0], $tree1,         'consumer call 2 arg pathUp[0]');

# -----------------------------------------------------------------------

$tree1 := [1, [2, [3, 4, 5], 6], 7];

@pcalls := [];
@ccalls := [];
&probe := -> $node, @pathUp {
    @pcalls.push([$node, nqp::clone(@pathUp)]);
    if nqp::islist($node) {
        TreeWalkDo.recurse(:take(!!@pathUp));
    } else {
        if $node == 4 {
            TreeWalkDo.break(:take);
        } else {
            TreeWalkDo.return(:take);
        }
    }
};

TreeWalk.dfs-up(&probe, &consumer, $tree1);

is(nqp::elems(@pcalls), 7, 'nr of calls to &probe')
    || diag(@pcalls);
is(nqp::elems(@ccalls), 6, 'nr of calls to &consumer')
    || diag(@ccalls);

# calls to &consumer
is(           @ccalls[0][0],    1,              'consumer call 1 arg node');
is(nqp::elems(@ccalls[0][1]),   1,              'consumer call 1 arg pathUp length');
is(           @ccalls[0][1][0], $tree1,         'consumer call 1 arg pathUp[0]');

is(           @ccalls[1][0],    2,              'consumer call 2 arg node');
is(nqp::elems(@ccalls[1][1]),   2,              'consumer call 2 arg pathUp length');
is(           @ccalls[1][1][0], $tree1[1],      'consumer call 2 arg pathUp[0]');
is(           @ccalls[1][1][1], $tree1,         'consumer call 2 arg pathUp[1]');

is(           @ccalls[2][0],    3,              'consumer call 3 arg node');
is(nqp::elems(@ccalls[2][1]),   3,              'consumer call 3 arg pathUp length');
is(           @ccalls[2][1][0], $tree1[1][1],   'consumer call 3 arg pathUp[0]');
is(           @ccalls[2][1][1], $tree1[1],      'consumer call 3 arg pathUp[1]');
is(           @ccalls[2][1][2], $tree1,         'consumer call 3 arg pathUp[2]');

is(           @ccalls[3][0],    4,              'consumer call 4 arg node');
is(nqp::elems(@ccalls[3][1]),   3,              'consumer call 4 arg pathUp length');
is(           @ccalls[3][1][0], $tree1[1][1],   'consumer call 4 arg pathUp[0]');
is(           @ccalls[3][1][1], $tree1[1],      'consumer call 4 arg pathUp[1]');
is(           @ccalls[3][1][2], $tree1,         'consumer call 4 arg pathUp[2]');

is(           @ccalls[4][0],    $tree1[1][1],   'consumer call 5 arg node');
is(nqp::elems(@ccalls[4][1]),   2,              'consumer call 5 arg pathUp length');
is(           @ccalls[4][1][0], $tree1[1],      'consumer call 5 arg pathUp[0]');
is(           @ccalls[4][1][1], $tree1,         'consumer call 5 arg pathUp[1]');

is(           @ccalls[5][0],    $tree1[1],      'consumer call 6 arg node');
is(nqp::elems(@ccalls[5][1]),   1,              'consumer call 6 arg pathUp length');
is(           @ccalls[5][1][0], $tree1,         'consumer call 6 arg pathUp[0]');

# -----------------------------------------------------------------------

$tree1 := [1, [2, [3, 4, 5], 6], 7];

@pcalls := [];
@ccalls := [];
&probe := -> $node, @pathUp {
    @pcalls.push([$node, nqp::clone(@pathUp)]);
    if nqp::islist($node) {
        TreeWalkDo.recurse(:take(!!@pathUp));
    } else {
        if $node == 4 {
            TreeWalkDo.halt(:take);     # <-------- halt instead of break
        } else {
            TreeWalkDo.return(:take);
        }
    }
};

TreeWalk.dfs-up(&probe, &consumer, $tree1);

is(nqp::elems(@pcalls), 7, 'nr of calls to &probe')
    || diag(@pcalls);
is(nqp::elems(@ccalls), 4, 'nr of calls to &consumer')
    || diag(@ccalls);

# calls to &consumer
is(           @ccalls[0][0],    1,              'consumer call 1 arg node');
is(nqp::elems(@ccalls[0][1]),   1,              'consumer call 1 arg pathUp length');
is(           @ccalls[0][1][0], $tree1,         'consumer call 1 arg pathUp[0]');

is(           @ccalls[1][0],    2,              'consumer call 2 arg node');
is(nqp::elems(@ccalls[1][1]),   2,              'consumer call 2 arg pathUp length');
is(           @ccalls[1][1][0], $tree1[1],      'consumer call 2 arg pathUp[0]');
is(           @ccalls[1][1][1], $tree1,         'consumer call 2 arg pathUp[1]');

is(           @ccalls[2][0],    3,              'consumer call 3 arg node');
is(nqp::elems(@ccalls[2][1]),   3,              'consumer call 3 arg pathUp length');
is(           @ccalls[2][1][0], $tree1[1][1],   'consumer call 3 arg pathUp[0]');
is(           @ccalls[2][1][1], $tree1[1],      'consumer call 3 arg pathUp[1]');
is(           @ccalls[2][1][2], $tree1,         'consumer call 3 arg pathUp[2]');

is(           @ccalls[3][0],    4,              'consumer call 4 arg node');
is(nqp::elems(@ccalls[3][1]),   3,              'consumer call 4 arg pathUp length');
is(           @ccalls[3][1][0], $tree1[1][1],   'consumer call 4 arg pathUp[0]');
is(           @ccalls[3][1][1], $tree1[1],      'consumer call 4 arg pathUp[1]');
is(           @ccalls[3][1][2], $tree1,         'consumer call 4 arg pathUp[2]');






done();
