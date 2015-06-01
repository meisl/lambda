#!nqp

use testing;

# Well, the testing stuff itself needs testing...
#
# In order to prove the test fns correct we need a way of asserting
# what they should do on various inputs.
# First off: whether they should fail or pass.
# But not only that - we also have to take into account exceptions
# and also the test_counter.
# The latter meaning: by how much should it be advanced in a certain
# situtation, if at all?

plan(119);


# Handy thing for keeping an eye on the test_counter.
# Note that we're not (yet) using `is` but rather do it all by hand,
# relying only on `ok`.
my int $tc;
sub testcounter_ok(int $how_many_more, $desc = NO_VALUE) {
    $desc := "test_counter+$how_many_more"
        if $desc =:= NO_VALUE;
    my int $actual := $test_counter;
    my int $expected := $tc + $how_many_more;
    my $result;

    #$result := is($actual, $expected, $desc);  # if we were to rely on `is` already
    
    $result := $actual == $expected;
    if $result {
        ok(1, $desc);
    } else {
        ok(0, "$desc\n  # expected (==): $expected"     # same as `is` would do,
                 ~ "\n  #           got: $actual"       # but simplified since we know it's ints
        );
    }
    $tc := $test_counter;   # update for next use
    $result;    # need to return this, *not* $tc!
}


# But: is `ok` really ok?
diag('sanity checks:');

my @arr := [];
$tc := $test_counter;   # initialize before first use
ok(@arr ?? 0 !! 1, 'empty array is falsey');
testcounter_ok(1, '`ok` advances test_counter by 1');

@arr.push(0);
ok(@arr ?? 1 !! 0, 'non-empty array is truthy');
testcounter_ok(1, '`ok` advances test_counter by 1');

@arr.pop;
ok(@arr ?? 0 !! 1, 'empty-again array is falsey');
testcounter_ok(1, '`ok` advances test_counter by 1');

# Hmm, `diag` isn't really a test fn, so:
diag('just calling diag to see if it (NOT!) advances the test_counter...');
testcounter_ok(0, '`diag` does not advance test_counter');


# Start off by checking for failure/passing of normal tests,
# keeping an eye on the test_counter:
diag('fails_ok/passes_ok on normal tests that actual pass or fail:');
diag('"ok XX test_counter+Y" means from now on: "inner tests are not counted on the outside (= as it should be)"');

my $passingS := 'ok(1, "foo")';
my $passing := { ok(1, "foo") };

my $failingS := 'ok(0, "bar")';
my $failing := { ok(0, "bar") };


passes_ok($passing, "'$passingS'");
testcounter_ok(1);

fails_ok($failing, "'$failingS'");
testcounter_ok(1);


# So... then why not check whether passes_ok passes when it should, etc?
diag('fails_ok/passes_ok on normal tests, nested 1 level:');

passes_ok({ passes_ok($passing, "'$passingS'") }, "'passes_ok(\{ $passingS })'");
testcounter_ok(1);

fails_ok({ passes_ok($failing, "'$failingS'") }, "'passes_ok(\{ $failingS })'");
testcounter_ok(1);

fails_ok({ fails_ok($passing, "'$passingS'") }, "'fails_ok(\{ $passingS })'");
testcounter_ok(1);

passes_ok({ fails_ok($failing, "'$failingS'") }, "'fails_ok(\{ $failingS })'");
testcounter_ok(1);


# This can be pushed further.
# Error msgs are becoming *real* fun now - try it by changing the outermost (top-level) assertion.
diag('fails_ok/passes_ok on normal tests, nested 2 levels:');

passes_ok({ passes_ok({ passes_ok($passing, "...") }, "...") }, "'passes_ok(\{ passes_ok(\{ $passingS }) })'");
testcounter_ok(1);

fails_ok({ passes_ok({ passes_ok($failing, "...") }, "...") },  "'passes_ok(\{ passes_ok(\{ $failingS }) })'");
testcounter_ok(1);

fails_ok({ passes_ok({ fails_ok($passing, "...") }, "...") },   "'passes_ok(\{ fails_ok(\{ $passingS }) })'");
testcounter_ok(1);

passes_ok({ passes_ok({ fails_ok($failing, "...") }, "...") },  "'passes_ok(\{ fails_ok(\{ $failingS }) })'");
testcounter_ok(1);
# ----------vvvvv-------------------------------------------------vvvvv
fails_ok({ fails_ok({ passes_ok($passing, "...") }, "...") },   "'fails_ok(\{ passes_ok(\{ $passingS }) })'");
testcounter_ok(1);

passes_ok({ fails_ok({ passes_ok($failing, "...") }, "...") },  "'fails_ok(\{ passes_ok(\{ $failingS }) })'");
testcounter_ok(1);

passes_ok({ fails_ok({ fails_ok($passing, "...") }, "...") },   "'fails_ok(\{ fails_ok(\{ $passingS }) })'");
testcounter_ok(1);

fails_ok({ fails_ok({ fails_ok($failing, "...") }, "...") },    "'fails_ok(\{ fails_ok(\{ $failingS }) })'");
testcounter_ok(1);


# Now let's specify what fails_ok/passes_ok should do when passed non-test code,
# ie code that does not call `ok` at all.
# Well, they should always fail, of course. But it's important NOT to take a truthy
# return value as test success, or a falsey one for test failure - just by itself.
# (Btw: to tell apart we use the dynamic @*TEST_OF_TEST - DO NOT MUCK WITH THAT!).
diag('fails_ok/passes_ok on bogus non-test code (need 1 level of nesting for this):');

my $notest_1S := '{ 1 }';
my $notest_1 := { 1 };

my $notest_0S := '{ 0 }';
my $notest_0 := { 0 };

my $notest_nullS := '{ nqp::null }';
my $notest_null := { nqp::null };


fails_ok({ passes_ok($notest_1, "'$notest_1S'") }, "'passes_ok($notest_1S, ...)'");
testcounter_ok(1);

fails_ok({ passes_ok($notest_0, "'$notest_0S'") }, "'passes_ok($notest_0S, ...)'");
testcounter_ok(1);

fails_ok({ passes_ok($notest_null, '"$notest_nullS"') }, "'passes_ok($notest_nullS, ...)'");
testcounter_ok(1);
# ---------vvvvv-----------------------------------vvvvv
fails_ok({ fails_ok($notest_1, "'$notest_1S'") }, "'fails_ok($notest_1S, ...)'");
testcounter_ok(1);

fails_ok({ fails_ok($notest_0, "'$notest_0S'") }, "'fails_ok($notest_0S, ...)'");
testcounter_ok(1);

fails_ok({ fails_ok($notest_null, "'$notest_nullS'") }, "'fails_ok($notest_nullS, ...)'");
testcounter_ok(1);


# Time for checking exceptions...
diag('lives_ok/dies_ok on normal non-test code:');

# direct tests (only positive tests possible):
lives_ok($notest_1, "'$notest_1S'");
testcounter_ok(1);

lives_ok({ $notest_0 }, "'$notest_0S'");
testcounter_ok(1);

lives_ok({ $notest_null }, "'$notest_nullS'");
testcounter_ok(1);

my $dyingS := '{ nqp::die("boom!") }';
my $dying := { nqp::die("boom!") };

dies_ok($dying, "'$dyingS'");
testcounter_ok(1);

# and now for indirect tests, ie including the negative tests:
# but first: positive tests repeated, indirect this time:
passes_ok({ lives_ok($notest_1, "'$notest_1S'") }, "'lives_ok($notest_1S, ...)'");
testcounter_ok(1);

passes_ok({ lives_ok($notest_0, "'$notest_0S'") }, "'lives_ok($notest_0S, ...)'");
testcounter_ok(1);

passes_ok({ lives_ok($notest_null, "'$notest_nullS'") }, "'lives_ok($notest_nullS, ...)'");
testcounter_ok(1);

passes_ok({ dies_ok($dying, "'$dyingS'") }, "'dies_ok($dyingS, ...)'");
testcounter_ok(1);

# negative tests, indirect:
fails_ok({ dies_ok($notest_1, "'$notest_1S'") }, "'dies_ok($notest_1S, ...)'");
testcounter_ok(1);

fails_ok({ dies_ok($notest_0, "'$notest_0S'") }, "'dies_ok($notest_0S, ...)'");
testcounter_ok(1);

fails_ok({ dies_ok($notest_null, "'$notest_nullS'") }, "'dies_ok($notest_nullS, ...)'");
testcounter_ok(1);

fails_ok({ lives_ok($dying, "'$dyingS'") }, "'lives_ok($dyingS, ...)'");
testcounter_ok(1);


# What about the test_counter when checking for exceptions?
diag('lives_ok/dies_ok on test code (which doesn\'t throw exceptions):');

# again, we do the direct tests first (not needing fails_ok/passes_ok)
lives_ok($passing, "'$passingS'");
testcounter_ok(1);

lives_ok($failing, "'$failingS'");
testcounter_ok(1);

# and now for indirect tests, ie including the negative tests:
# but first: positive tests repeated, indirect this time:
passes_ok({ lives_ok($passing, "'$passingS'") }, "'lives_ok($passingS, ...)'");
testcounter_ok(1);

passes_ok({ lives_ok($failing, "'$failingS'") }, "'lives_ok($failingS, ...)'");
testcounter_ok(1);

# negative tests, indirect:
fails_ok({ dies_ok($passing, "'$passingS'") }, "'dies_ok($passingS, ...)'");
testcounter_ok(1);

fails_ok({ dies_ok($failing, "'$failingS'") }, "'dies_ok($failingS, ...)'");
testcounter_ok(1);



# Then there's exceptions thrown from the test fns themselves...
diag('lives_ok/dies_ok on test code (which *does* throw exceptions):');

# again, we do the direct tests first (not needing fails_ok/passes_ok [on the outside, that is])
my $passingThenDyingS := '{ ok(1); nqp::die("boom!"); }';
my $passingThenDying   := { ok(1); nqp::die("boom!"); };

my $failingThenDyingS := '{ ok(0); nqp::die("boom!"); }';
my $failingThenDying   := { ok(0); nqp::die("boom!"); };

dies_ok($passingThenDying, "'$passingThenDyingS'");
testcounter_ok(1);

dies_ok($failingThenDying, "'$failingThenDyingS'");
testcounter_ok(1);

# and now for indirect tests, ie including the negative tests:
# but first: positive tests repeated, indirect this time:
passes_ok({ dies_ok($passingThenDying, "'$passingThenDyingS'") }, "'dies_ok($passingThenDyingS, ...)'");
testcounter_ok(1);

passes_ok({ dies_ok($failingThenDying, "'$failingThenDyingS'") }, "'dies_ok($failingThenDyingS, ...)'");
testcounter_ok(1);

# negative tests, indirect:
fails_ok({ lives_ok($passingThenDying, "'$passingThenDyingS'") }, "'lives_ok($passingThenDyingS, ...)'");
testcounter_ok(1);

fails_ok({ lives_ok($failingThenDying, "'$failingThenDyingS'") }, "'lives_ok($failingThenDyingS, ...)'");
testcounter_ok(1);


# Stop the toying now, here's when fails_ok/passes should throw:
diag('fails_ok/passes_ok should throw when given non-invokable 1st arg:');
# TODO: check error msgs (should say it's not invokable)

dies_ok({ fails_ok(0, "literal 0") },               "'fails_ok(0, ...)'");
testcounter_ok(1);

dies_ok({ fails_ok(1, "literal 1") },               "'fails_ok(1, ...)'");
testcounter_ok(1);

dies_ok({ fails_ok("foo", "literal \"foo\"") },     "'fails_ok(\"foo\", ...)'");
testcounter_ok(1);

dies_ok({ fails_ok(nqp::null, "nqp::null") },       "'fails_ok(nqp::null, ...)'");
testcounter_ok(1);
# --------vvvvv---------------------------------------vvvvvv
dies_ok({ passes_ok(0, "literal 0") },              "'passes_ok(0, ...)'");
testcounter_ok(1);

dies_ok({ passes_ok(1, "literal 1") },              "'passes_ok(1, ...)'");
testcounter_ok(1);

dies_ok({ passes_ok("foo", "literal \"foo\"") },    "'passes_ok(\"foo\", ...)'");
testcounter_ok(1);

dies_ok({ passes_ok(nqp::null, "nqp::null") },      "'passes_ok(nqp::null, ...)'");
testcounter_ok(1);


diag('fails_ok/passes_ok should throw when given invokable 1st arg which is non-0-arity:');
# TODO: check error msgs (should say it's not invokable)

my $unaryS := '-> $x { $x }';
my $unary  :=  -> $x { $x };

# We should be able to differentiate between the above (plain misuse of fails_ok/passes/ok)
# and a proper nullary, which, when called with no args throws *from within it*:
my $nullaryBoomS := '-> { nqp::die("boom!") }';
my $nullaryBoom  :=  -> { nqp::die("boom!") };

# Also, it could be a proper nullary, which when called with no args, 
# triggers *within it* a 'Too few positionals passed; ...':
my $nullaryTrickyBoomS := "-> \{ $unaryS() }";
my $nullaryTrickyBoom  :=  ->  { $unary()  };

# Finally, a proper nullary could, when called with no args, 
# literally throw a 'Too few positionals passed; expected 1 argument but got 0'
# - right there (thereby lying, kind of).
# Well, that's the point where we have to give up...
my $nullaryViciousBoomS := '-> { nqp::die("Too few positionals passed; expected 1 argument but got 0") }';
my $nullaryViciousBoom  :=  -> { nqp::die("Too few positionals passed; expected 1 argument but got 0") }; 


##passes_ok($unary, "'$unaryS'");    # dies as it should
dies_ok({ passes_ok($unary, "'$unaryS'") }, "'passes_ok($unaryS, ...)'");
testcounter_ok(1);

##passes_ok($nullaryBoom, "'$nullaryBoomS'");    # fails as it should
fails_ok({ passes_ok($nullaryBoom, "'$nullaryBoomS'") }, "'passes_ok($nullaryBoomS, ...)'");
testcounter_ok(1);

##passes_ok($nullaryTrickyBoom, "'$nullaryTrickyBoomS'");    # fails as it should
fails_ok({ passes_ok($nullaryTrickyBoom, "'$nullaryTrickyBoomS'") }, "'passes_ok($nullaryTrickyBoomS, ...)'");
testcounter_ok(1);

## Here we must give up - it is simply lying!
##passes_ok($nullaryViciousBoom, "'$nullaryViciousBoomS'");   # dies as if we passed a non-nullary
dies_ok({ passes_ok($nullaryViciousBoom, "'$nullaryViciousBoomS'") }, "'passes_ok($nullaryViciousBoomS, ...)'");
testcounter_ok(1);

# TODO: same with fails_ok, then dies_ok and lives_ok, too
# --------vvvvv---------------------------------------vvvvvv



#is_eq("asdf", "asdf", "should fail");
#is_eq(1, "asdf", "should throw");
