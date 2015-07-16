#!nqp

use Util;
use Backtrace;


my @*TEST_OF_TEST := [];


# Don't export this - only a workaround for the weird problems with exporting subs
# (can call them from outside but then they in turn cannot call themselves)
class Testing {
    
    my $test_counter  := 0;
    my $tests_planned := 0;
    my @tests_failed  := [];

    method test_counter() { $test_counter }

    method diag($thing) {
        my $msg;
        if nqp::isstr($thing) {
            $msg := $thing;
        } else {
            $msg := describe($thing);
        }
        my @lines := nqp::split("\n", $msg);
        say('# ' ~ nqp::join("\n# ", @lines));
        #say("# $msg");
    }

    method plan(int $nr_of_tests) {
        $tests_planned := $nr_of_tests;
        say("1..$nr_of_tests");
    }

    method ok($condition, $desc, *@descX) {
        $test_counter++;    # yes, even if +@*TEST_OF_TEST - so we can tell apart proper tests and other stuff (possibly returning 1)

        my @output;
        my $failureat;
        unless $condition {
            @output.push("not ");
            $failureat := Backtrace.new(:skip(+@*TEST_OF_TEST == 0 ?? 1 !! 0));
        }
        @output.push("ok $test_counter");
        if $desc {
            @output.push(" - $desc");
        }

        @descX.unshift('');
        @output.push(join(
            "\n  # ", @descX,
            :map(-> $x { nqp::istype($x, Backtrace)
                            ?? '#' ~ $x.filter.Str(:prefix("  # #"))
                            !! ~$x;
            }),
        ));

        if @*TEST_OF_TEST {
            my $from := @*TEST_OF_TEST.pop;
            my %outcome := hash(
                :$from,
                :$condition,
                :description($desc),
                :output(nqp::join('', @output)),
            );
            unless $condition {
                %outcome<failureat> := $failureat;
            }
            
            @*TEST_OF_TEST.push(%outcome);
        } else {
            unless $condition {
                #$failureat := $failureat.filter();
                # TODO: filter out frames from this file - under circumstances (...!)
                #$failureat := $failureat.filter(-> $f {$f<file> ne self.FILE});
                @output.push("\n" ~ $failureat.Str(:prefix("  #"), :prefix1st));
                @tests_failed.push(hash(
                    :nr($test_counter),
                    :backtrace($failureat),
                    :description($desc),
                ));
            }
            say(|@output);
        }
        $condition ?? 1 !! 0;
    }

    method done() {
        my @out := ['', ''];
        if $test_counter == $tests_planned {
            @out[1] := "Ran $test_counter tests";
        } else {
            @out[1] := "Looks like you planned $tests_planned tests, but ran $test_counter";
        }
        if @tests_failed {
            @out[1] := @out[1] ~ " - of which {+@tests_failed} FAILED:";
        } else {
            @out[1] := @out[1] ~ " (all passed).";
        }
        @out[0] := nqp::x('=', nqp::chars(@out[1]));
        if @tests_failed {
            my @numbers := [];
            for @tests_failed {
                @numbers.push(~$_<nr>);
                my $desc := $_<description> // '';
                if $desc {
                    my $firstNL := nqp::index($desc, "\n");
                    $firstNL := nqp::chars($desc) if $firstNL < 0;
                    $desc := ' - ' ~ nqp::substr($desc, 0, $firstNL);
                }
                my $frame := $_<backtrace>[$_<backtrace>.list - 1];
                @out.push($_<nr> ~ ' at ' ~ $frame ~ $desc);
            }
            @out[1] := @out[1] ~ ' ' ~ nqp::join(', ', @numbers);
        }
        self.diag(nqp::join("\n", @out));
    }

    # In order to tell apart whether
    #   a) $code is not nullary (and therefore throws) or
    #   b) $code *is* nullary but an exception is thrown from within it
    # ...we provoke a "Too few positionals..."-exception ourselves,
    # right here, and catch and store it in $myX.
    # Then we call $code with no args and if that indeed dies we compare
    # its exception ($theirX) with $myX.
    method invokeNullaryChecked($code) {
        my $returnValue;
        my $becauseNonNullary;
        my $theirX := NO_VALUE;
        my $myX;
        my $theirBacktrace;
        my $myBacktrace;
        try {
            # 
            # So: >>>> the following *MUST BE KEPT ON THE VERY SAME LINE!* <<<<
            try { -> $_ {}(); CATCH { $myX := $! } }; $returnValue := $code(); 
            
            CATCH {
                $theirX := $!;   # store the error from calling $code with no args
                
                # strange: MUST take backtraces here in this CATCH or else lines are confused
                $myBacktrace    := Backtrace.new($myX);
                $theirBacktrace := Backtrace.new($theirX);
            }
       };

        if $theirX =:= NO_VALUE { # calling $code did NOT yield an exception -> must have a return value
            return hash(
                :returned($returnValue),
            );
        } else {    # calling $code DID yield an exception -> find out why
            # If indeed non-0-arity is the problem then 1st frame is at the start of block and 2nd is our call above
            my $myFrame     := $myBacktrace[1];
            my $theirFrame  := $theirBacktrace[1];
            
            # use file plus line plus message to identify where and what was thrown
            my $mine := $myFrame<file>    ~ ':' ~ $myFrame<line>    ~ ':"' ~ nqp::escape(~$myX) ~ '"';
            my $them := $theirFrame<file> ~ ':' ~ $theirFrame<line> ~ ':"' ~ nqp::escape(~$theirX) ~ '"';
            
            # Finally, their being equal we take as indication that it was our call with no args
            # that triggered the exception (meaning that $code indeed expects args).
            # Note: it is still possible that $code is actually nullary but contains a literal
            #       `nqp::die("Too few positionals passed; expected 1 argument but got 0)"`
            #       on the top level - in which case it is simply lying, and we just cannot tell.
            $becauseNonNullary := $mine eq $them;
            
            return hash(
                :error($theirX),
                :$becauseNonNullary,
                :backtrace($theirBacktrace)
            );
        }
    }

    method fails_ok($block, $desc) {
        nqp::die('fails_ok expects an invokable object as first arg - got: ' ~ describe($block))
            unless nqp::isinvokable($block);

        my $tc := $test_counter;
        my $depth := +@*TEST_OF_TEST;
        @*TEST_OF_TEST.push('fails_ok');                                       # REFACTOR: "fails_ok" -> "passes_ok"
        
        $desc := $desc ~ ' fails';                                             # REFACTOR: "fails" -> "passes"
        my $result;
        my @descX := [];
        
        my %block_outcome := self.invokeNullaryChecked($block);
        my $error := %block_outcome<error>;
        if $error {
            if %block_outcome<becauseNonNullary> { # we've been passed an inappropriate $block
                # cleanup 
                nqp::setelems(@*TEST_OF_TEST, $depth);
                $test_counter := $tc;
                # ...and complain
                nqp::die('fails_ok expects a nullary invokable as first arg - "' ~ nqp::escape($error) ~ '"');
            } else { # $block died inside it -> we fail with appropriate message
                $result := 0;
                @descX := [
                    "should fail but died: '"  ~ nqp::escape($error) ~ "'",
                    %block_outcome<backtrace>,
                ];
            }
        } else { # $block did not die -> must have returned something
            my $block_returned := %block_outcome<returned>;
            # Now check if there were tests and if so, whether they passed
            my $inner_tests_outcome := (+@*TEST_OF_TEST == $depth + 1) && @*TEST_OF_TEST.pop;
            if nqp::ishash($inner_tests_outcome) {  # $block actually did contain tests
                if $block_returned {
                    $result := 0;
                    @descX := [ "should fail but passed: '" ~ nqp::escape($inner_tests_outcome<output>) ~ "'" ];
                } else {
                    $result := 1;
                }
            } else {    # looks like no tests in $block
                $result := 0;
                if $tc == $test_counter {
                    @descX := [
                        "should fail but no tests",
                        "returned: '" ~ describe($block_returned),
                    ];
                } else {
                    @descX := [
                        "should fail but broke test-of-test protocol",
                        "inner tests: " ~ ($test_counter - $tc) ~ ' (it seems...)',
                        "   returned: " ~ describe($block_returned),
                        "testoftests: " ~ $depth,
                    ];
                }
            }
        }

        # clean up
        nqp::setelems(@*TEST_OF_TEST, $depth);
        $test_counter := $tc;

        self.ok($result, $desc, |@descX);
    }

    method passes_ok($block, $desc) {
        nqp::die('passes_ok expects an invokable object as first arg - got: ' ~ describe($block))
            unless nqp::isinvokable($block);

        my $tc := $test_counter;
        my $depth := +@*TEST_OF_TEST;
        @*TEST_OF_TEST.push('passes_ok');                                       # REFACTOR: "fails_ok" -> "passes_ok"
        
        $desc := $desc ~ ' passes';                                             # REFACTOR: "fails" -> "passes"
        my $result;
        my @descX := [];
        
        my %block_outcome := self.invokeNullaryChecked($block);
        my $error := %block_outcome<error>;
        if $error {
            if %block_outcome<becauseNonNullary> { # we've been passed an inappropriate $block
                # cleanup 
                nqp::setelems(@*TEST_OF_TEST, $depth);
                $test_counter := $tc;
                # ...and complain
                nqp::die('passes_ok expects a nullary invokable as first arg - "' ~ nqp::escape($error) ~ '"');
            } else { # $block died inside it -> we fail with appropriate message
                $result := 0;
                @descX := [
                    "should pass but died: '"  ~ nqp::escape($error) ~ "'",
                    %block_outcome<backtrace>,
                ];
            }
        } else { # $block did not die -> must have returned something
            my $block_returned := %block_outcome<returned>;
            # Now check if there were tests and if so, whether they passed
            my $inner_tests_outcome := (+@*TEST_OF_TEST == $depth + 1) && @*TEST_OF_TEST.pop;
            if nqp::ishash($inner_tests_outcome) {  # $block actually did contain tests
                if !$block_returned {                                           # REFACTOR: $block_returned -> !$block_returned
                    $result := 0;   # we fail if test(s) in $block failed
                    @descX := [
                        "should pass but failed: '" ~ nqp::escape($inner_tests_outcome<output>) ~ "'",
                        $inner_tests_outcome<failureat>
                    ];
                } else {
                    $result := 1;   # we pass if test(s) in $block passed
                }
            } else {    # looks like no tests in $block
                $result := 0;   # we fail, for sure
                if $tc == $test_counter {   # seems $block simply did not contain any test code
                    @descX := [
                        "should pass but no tests",                      # REFACTOR: "fail" -> "pass"
                        "returned: '" ~ describe($block_returned),
                    ];
                } else {    # worse: something's deeply broken with the test-of-test protocol - or we're being fooled...
                    @descX := [
                        "should pass but broke test-of-test protocol",   # REFACTOR: "fail" -> "pass"
                        "inner tests: " ~ ($test_counter - $tc) ~ ' (it seems...)',
                        "   returned: " ~ describe($block_returned),
                        "testoftests: " ~ $depth,
                    ];
                }
            }
        }

        # clean up
        nqp::setelems(@*TEST_OF_TEST, $depth);
        $test_counter := $tc;

        self.ok($result, $desc, |@descX);
    }

    method lives_ok($block, $desc) {
        nqp::die('lives_ok expects an invokable object as first arg - got: ' ~ describe($block))
            unless nqp::isinvokable($block);

        my $tc := $test_counter;
        my $depth := +@*TEST_OF_TEST;
        @*TEST_OF_TEST.push('lives_ok');
        
        $desc := $desc ~ ' lives';
        my $result;
        my @descX := [];
        
        my %block_outcome := self.invokeNullaryChecked($block);
        my $error := %block_outcome<error>;
        if $error {
            $result := 0;
            if %block_outcome<becauseNonNullary> { # we've been passed an inappropriate $block
                # cleanup 
                nqp::setelems(@*TEST_OF_TEST, $depth);
                $test_counter := $tc;
                # ...and complain
                nqp::die('lives_ok expects a nullary invokable as first arg - "' ~ nqp::escape($error) ~ '"');
            } else { # $block died inside it -> we fail with appropriate message
                @descX := [
                    "should live but died: '"  ~ nqp::escape($error) ~ "'",
                    %block_outcome<backtrace>,
                ];
            }
        } else {
            $result := 1;
        }
        
        # clean up
        nqp::setelems(@*TEST_OF_TEST, $depth);
        $test_counter := $tc;
        
        self.ok($result, $desc, |@descX);
    }

    method dies_ok($block, $desc) {
        nqp::die('dies_ok expects an invokable object as first arg - got: ' ~ describe($block))
            unless nqp::isinvokable($block);
        
        my $tc := $test_counter;
        my $depth := +@*TEST_OF_TEST;
        @*TEST_OF_TEST.push('dies_ok');
        
        $desc := $desc ~ ' dies';
        my $result;
        my @descX := [];
        
        my %block_outcome := self.invokeNullaryChecked($block);
        my $error := %block_outcome<error>;
        if $error {
            if %block_outcome<becauseNonNullary> { # we've been passed an inappropriate $block
                # cleanup 
                nqp::setelems(@*TEST_OF_TEST, $depth);
                $test_counter := $tc;
                # ...and complain
                nqp::die('dies_ok expects a nullary invokable as first arg - "' ~ nqp::escape($error) ~ '"');
            } else { # $block died inside it -> we pass
                $result := 1;
            }
        } else {
            $result := 0;
            @descX := ['should die but returned: ' ~ describe(%block_outcome<returned>)];
        }

        # clean up
        nqp::setelems(@*TEST_OF_TEST, $depth);
        $test_counter := $tc;

        self.ok($result, $desc, |@descX);
    }
    
    sub test_is($actual, $expected) {
        my $result;
        my $comp;
        if nqp::isstr($expected) {
            if nqp::isstr($actual) {
                if nqp::isnull_s($expected) {
                    $result := nqp::isnull_s($actual);
                } elsif nqp::isnull_s($actual) {
                    $result := 0;
                } else {
                    $result := $actual eq $expected;
                }
            } else {
                $result := 0;
            }
            $comp := 'eq';
        } elsif nqp::isint($expected) {
            $result := (nqp::isint($actual) || nqp::isnum($actual)) && $actual == $expected;
            $comp := '==';
        } elsif nqp::isnum($expected) {
            $result := (nqp::isnum($actual) || nqp::isint($actual)) && $actual == $expected;
            $comp := '==';
        } else {
            $result := $actual =:= $expected;
            $comp := '=:=';
        }
        nqp::hash('result', $result, 'comp', $comp);
    }

    method is($actual, $expected, $desc) {
        my $test := test_is($actual, $expected);
        unless $test<result> {
            $desc := $desc ~ "\n  # expected (" ~ $test<comp> ~ '): ' ~ describe($expected)
                           ~ "\n  #" ~ nqp::x(' ', nqp::chars($test<comp>) + 9) ~ "got: " ~ describe($actual)
            ;
        }
        self.ok($test<result>, $desc);
    }

    method isnt($actual, $expected, $desc) {
        my $test := test_is($actual, $expected);
        if $test<result> {
            $desc := $desc ~ "\n  # expected anything but (" ~ $test<comp> ~ '): ' ~ describe($expected)
                           ~ "\n  #" ~ nqp::x(' ', nqp::chars($test<comp>) + 22) ~ "got: the very same"
            ;
        }
        self.ok(!$test<result>, $desc);
    }

    method is_same($actual, $expected, $desc) {
        my $result := $actual =:= $expected;
        unless $result {
            $desc := $desc ~ "\n  # expected (=:=): $expected"
                           ~ "\n  #            got: $actual"
            ;
        }
        self.ok($result, $desc);
    }

    method is_eq($actual, $expected, str $desc) {
        try {
            my str $a := $actual;
            my str $x := $expected;
            self.ok($a eq $x, $desc);
            CATCH { self.ok(0, $desc) }
        }
    }


    method isa_ok($actual, $expectedType, str $desc, *%attributes) {
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
        if $result && %attributes {
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
                        unless self.is($av, $xv, $d) {
                            $desc := $d;
                            $result := 0;
                        }
                    } else {
                        $desc := $desc ~ "\n  # expected: a " ~ $expectedType.HOW.name($expectedType)
                                            ~ " where .$m is " ~ describe($xv)
                                       ~ "\n  #   actual: " ~ describe($actual)
                                       ~ "\n  #      got: \"Cannot find method $m\""
                        ;
                        $result := self.ok(0, $desc);
                    }
                }
                $result;
            };
            return self.passes_ok($tests, $desc);
        } else {
            $desc := $desc ~ "\n  # expected: a " ~ $expectedType.HOW.name($expectedType)
                           ~ "\n  #      got: " ~ describe($actual)
                unless $result;
            return self.ok($result, $desc);
        }
    }


    method isa_nok($actual, $refutedType, str $desc) {
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
            $desc := $desc ~ "\n  # expected: anything but a " ~ $refutedType.HOW.name($refutedType)
                           ~ "\n  #      got: " ~ describe($actual)
            ;
        }
        self.ok($result, $desc);
    }



    my $HERE;
    method HERE() {
        $HERE := Backtrace.new unless $HERE;
        $HERE;
    }

    method FILE() {
        self.HERE[0]<file>;
    }
}


sub diag($msg)                          is export { Testing.diag($msg) }
sub plan($nr_of_tests)                  is export { Testing.plan($nr_of_tests) }
sub done()                              is export { Testing.done() }
sub ok($condition, $desc = NO_VALUE)    is export { Testing.ok($condition, $desc) }
sub fails_ok($block, $desc?)            is export { Testing.fails_ok($block, $desc) }
sub passes_ok($block, $desc?)           is export { Testing.passes_ok($block, $desc) }
sub lives_ok($block, $desc?)            is export { Testing.lives_ok($block, $desc) }
sub dies_ok($block, $desc?)             is export { Testing.dies_ok($block, $desc) }
sub is($actual, $expected, $desc?)      is export { Testing.is($actual, $expected, $desc) }
sub isnt($actual, $expected, $desc?)    is export { Testing.isnt($actual, $expected, $desc) }
sub isa_ok($actual, $expectedType, $desc, *%attributes) is export { Testing.isa_ok($actual, $expectedType, $desc, |%attributes) }
sub isa_nok($actual, $refutedType, $desc)               is export { Testing.isa_nok($actual, $refutedType, $desc); }


sub MAIN(*@ARGS) {
    #diag("Testing.HERE:\n" ~ Testing.HERE);
    #ok(0, '"ok(0)"');
    #passes_ok(
    #    { ok(0, '"ok(0)"') }, 
    #    'ok(0)');

    #my $bt := Testing::Backtrace.new(:skip(0));
    #say($bt);
    #say('');
    #say($bt.filter(-> $x { $x<file> ne Testing.FILE }));

    my $boom := { nqp::die("BOOM!") };
    my $bang := -> $x { "BANG!" };
    fails_ok($boom);
    passes_ok($boom);
    done();
}

