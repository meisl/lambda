#!nqp

my @*TEST_OF_TEST := [];


# Don't export this - only a workaround for the weird problems with exporting subs
# (can call them from outside but then they in turn cannot call themselves)
class Testing {
    
    my $tests_planned := 0;
    my $test_counter := 0;

    method test_counter() { $test_counter }

    method say(*@pieces) {
        my $s := '';
        for @pieces {
            $s := $s ~ $_;
        }
        nqp::say($s);
    }


    method diag($msg) {
        self.say("# $msg");
    }

    method describe($x) {
        my $out;
        if nqp::isint($x) {
            $out := "$x (int)";
        } elsif nqp::isnum($x) {
            $out := "$x (num)";
        } elsif nqp::isstr($x) {
            if nqp::isnull_s($x) {
                $out := 'nqp::null_s (str)';
            } else {
                $out := '"' ~ nqp::escape($x) ~ '" (str)';
            }
        } elsif nqp::isnull($x) {   # note: nqp::null_s would NOT pass the nqp::isnull test
            $out := 'nqp::null';
        } elsif nqp::ishash($x) {
            $out := 'nqp::hash(';
            my @pairs := [];
            for $x {
                my $k := nqp::iterkey_s($_);
                my $v := nqp::iterval($_);
                @pairs.push($k);
                @pairs.push(self.describe($v));
            }
            $out := $out ~ nqp::join(', ', @pairs) ~ ')';
        } else {
            my $how := nqp::how($x);
            if $how {
                $out := $how.name($x);
            } else {
                $out := nqp::reprname($x);
            }
            
            unless nqp::isconcrete($x) {
                $out := $out ~ ', Type object'
            }
            if nqp::isinvokable($x) {
                $out := $out ~ ', invokable';
            }
            $out := (nqp::can($x, 'Str') ?? $x.Str ~ ' ' !! '') ~ "($out)";
        }
        $out;
    }

    method plan(int $nr_of_tests) {
        $tests_planned := $nr_of_tests;
        self.say("1..$nr_of_tests");
    }

    method done() {
        unless $test_counter == $tests_planned {
            self.diag("Looks like you planned $tests_planned tests, but ran $test_counter");
        }
    }

    method ok($condition, $desc?) {
        $test_counter++;    # yes, even if +@*TEST_OF_TEST - so we can tell apart proper tests and other stuff (possibly returning 1)

        my @output;
        unless $condition {
            @output.push("not ");
        }
        @output.push("ok $test_counter");
        if $desc {
            @output.push(" - $desc");
        }
        if $test_counter <= $todo_upto_test_num {
            @output.push($todo_reason);
        }
        if @*TEST_OF_TEST {
            my $from := @*TEST_OF_TEST.pop;
            @*TEST_OF_TEST.push(hash(
                :$from,
                :$condition,
                :description($desc),
                :output(nqp::join('', @output)),
            ));
        } else {
            self.say(|@output);
        }
        $condition ?? 1 !! 0;
    }

    method invokeNullaryChecked($code) {
        my $error := NO_VALUE;
        my $returnValue;
        my $becauseNonNullary;
        try {
            my $x;
            # In order to tell apart whether
            #   a) $code is not nullary (and therefore throws) or
            #   b) $code *is* nullary but an exception is thrown from within it
            # ...we provoke a "Too few positionals..."-exception ourselves,
            # right here, and catch and store it in $x.
            # The we call $code with no args and if that indeed dies we compare 
            # its backtrace and msg with those of $x.
            # 
            # So: >>>> the following *MUST BE KEPT ON THE VERY SAME LINE!* <<<<
            try { -> $_ {}(); CATCH { $x := $! } }; $returnValue := $code();
            
            CATCH {
                # store the error from calling $code with no args
                $error := $!;
                
                # get info of the relevant backtrace frames
                my $mine := nqp::backtrace($x)[0]<annotations>;
                my $them := nqp::backtrace($!)[1]<annotations>; # one more frame on top for our call
                
                # use file plus line plus message to identify where and what was thrown
                $mine := $mine<file> ~ ':' ~ $mine<line> ~ ':"' ~ nqp::escape(~$x) ~ '"';
                $them := $them<file> ~ ':' ~ $them<line> ~ ':"' ~ nqp::escape(~$!) ~ '"';
                
                # Finally, their being equal we take as indication that it was our call with no args
                # that triggered the exception (meaning that $code indeed expects args).
                # Note: it is still possible that $code is actually nullary but contains a literal
                #       `nqp::die("Too few positionals passed; expected 1 argument but got 0)"`
                #       on the top level - in which case it is simply lying, and we just cannot tell.
                $becauseNonNullary := $mine eq $them;
            }
        }
        if $error =:= NO_VALUE { # calling $code did NOT yield an exception -> must have a return value
            return hash(
                :error(nqp::null),
                :returned($returnValue),
            );
        } else {    # calling $code DID yield an exception -> tell why
            return hash(
                :error($error),
                :$becauseNonNullary
            );
        }
    }

    method fails_ok($block, $desc) {
        nqp::die('fails_ok expects an invokable object as first arg - got: ' ~ self.describe($block))
            unless nqp::isinvokable($block);
        
        my $tc := $test_counter;
        my $depth := +@*TEST_OF_TEST;
        @*TEST_OF_TEST.push('fails_ok');
        $desc := $desc ~ ' fails';
        my $result := NO_VALUE;
        my $error  := NO_VALUE;
        my $inner_returned;
        try {
            $inner_returned := $block();
            CATCH {
                $result := 0;
                $error  := $!;
                $desc := "$desc\n  # should fail but died: '" ~ nqp::escape($error) ~ "'" 
                            ~ "\n    # " ~ nqp::join("\n    # ", nqp::backtracestrings($error))
                ;
            }
        }
        if $result =:= NO_VALUE { # did not throw
            my $inner_outcome := (+@*TEST_OF_TEST == $depth + 1) && @*TEST_OF_TEST.pop;
            if nqp::ishash($inner_outcome) {
                if $inner_returned {
                    $result := 0;
                    $desc := "$desc\n  # should fail but passed: " 
                           ~ '"' ~ nqp::escape($inner_outcome<output>) ~ '"'
                    ;
                } else {
                    $result := 1;
                }
            } else {
                $result := 0;
                if $tc == $test_counter {
                    $desc := $desc
                        ~ "\n  # should fail but no tests"
                        ~ "\n  # returned: '" ~ self.describe($inner_returned)
                    ;
                } else {
                    $desc := $desc
                        ~ "\n  # should fail but broke test-of-test protocol"
                        ~ "\n  # inner tests: " ~ ($test_counter - $tc) ~ ' (it seems...)'
                        ~ "\n  #    returned: " ~ self.describe($inner_returned)
                        ~ "\n  # testoftests: " ~ $depth
                    ;
                }
            }
        }

        # clean up
        nqp::setelems(@*TEST_OF_TEST, $depth);
        $test_counter := $tc;
        self.ok($result, $desc);
    }

    method passes_ok($block, $desc) {
        nqp::die('passes_ok expects an invokable object as first arg - got: ' ~ self.describe($block))
            unless nqp::isinvokable($block);

        my $tc := $test_counter;
        my $depth := +@*TEST_OF_TEST;
        @*TEST_OF_TEST.push('passes_ok');                                       # REFACTOR: "fails_ok" -> "passes_ok"
        
        $desc := $desc ~ ' passes';                                             # REFACTOR: "fails" -> "passes"
        my $result;
        
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
                $desc := "$desc\n  # should pass but died: '"                   # REFACTOR: "fail" -> "pass"
                                     ~ nqp::escape($error) ~ "'"
                            ~ "\n    # " ~ nqp::join("\n    # ", nqp::backtracestrings($error))
                ;
            }
        } else { # $block did not die -> must have returned something
            my $block_returned := %block_outcome<returned>;
            # Now check if there were tests and if so, whether they passed
            my $inner_tests_outcome := (+@*TEST_OF_TEST == $depth + 1) && @*TEST_OF_TEST.pop;
            if nqp::ishash($inner_tests_outcome) {  # $block actually did contain tests
                if !$block_returned {                                           # REFACTOR: $block_returned -> !$block_returned
                    $result := 0;   # we fail if test(s) in $block failed
                    $desc := "$desc\n  # should pass but failed: "              # REFACTOR: "fail but passed" -> "pass but failed"
                           ~ '"' ~ nqp::escape($inner_tests_outcome<output>) ~ '"'
                    ;
                } else {
                    $result := 1;   # we pass if test(s) in $block passed
                }
            } else {    # looks like no tests in $block
                $result := 0;   # we fail, for sure
                if $tc == $test_counter {   # seems $block simply did not contain any test code
                    $desc := $desc
                        ~ "\n  # should pass but no tests"                      # REFACTOR: "fail" -> "pass"
                        ~ "\n  # returned: '" ~ self.describe($block_returned)
                    ;
                } else {    # worse: something's deeply broken with the test-of-test protocol - or we're being fooled...
                    $desc := $desc
                        ~ "\n  # should pass but broke test-of-test protocol"   # REFACTOR: "fail" -> "pass"
                        ~ "\n  # inner tests: " ~ ($test_counter - $tc) ~ ' (it seems...)'
                        ~ "\n  #    returned: " ~ self.describe($block_returned)
                        ~ "\n  # testoftests: " ~ $depth
                    ;
                }
            }
        }

        # clean up
        nqp::setelems(@*TEST_OF_TEST, $depth);
        $test_counter := $tc;

        self.ok($result, $desc);
    }

    method lives_ok($block, $desc) {
        my $tc := $test_counter;
        my $depth := +@*TEST_OF_TEST;
        @*TEST_OF_TEST.push('passes_ok');   # REFACTOR!
        $desc := $desc ~ ' lives';
        my $result := NO_VALUE;
        my $error  := NO_VALUE;
        my $inner_returned;
        try {
            $inner_returned := $block();
            $result := 1;
            CATCH {
                $result := 0;
                $error  := $!;
                $desc := "$desc\n  # should live but died: '" ~ nqp::escape(~$error) ~ "'"
                            ~ "\n    # " ~ nqp::join("\n    # ", nqp::backtracestrings($error))
                ;
            }
        }

        # clean up
        nqp::setelems(@*TEST_OF_TEST, $depth);
        $test_counter := $tc;
        self.ok($result, $desc);
    }

    method dies_ok($block, $desc) {
        my $tc := $test_counter;
        my $depth := +@*TEST_OF_TEST;
        @*TEST_OF_TEST.push('passes_ok');   # REFACTOR!
        $desc := $desc ~ ' dies';
        my $result := NO_VALUE;
        my $error  := NO_VALUE;
        my $inner_returned;
        try {
            $inner_returned := $block();
            $result := 0;
            $desc := "$desc\n  # should die but returned: " ~ self.describe($inner_returned);
            CATCH {
                $result := 1;
                $error  := $!;
            }
        }

        # clean up
        nqp::setelems(@*TEST_OF_TEST, $depth);
        $test_counter := $tc;
        self.ok($result, $desc);
    }

    method is($actual, $expected, $desc) {
        my $result;
        my $comp;
        if nqp::isstr($expected) {
            $result := nqp::isstr($actual) && $actual eq $expected;
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
        unless $result {
            $desc := $desc ~ "\n  # expected ($comp): " ~ self.describe($expected)
                           ~ "\n  #" ~ nqp::x(' ', nqp::chars($comp) + 9) ~ "got: " ~ self.describe($actual)
            ;
        }
        self.ok($result, $desc);
    }

    sub is_same($actual, $expected, $desc) {
        my $result := $actual =:= $expected;
        unless $result {
            $desc := $desc ~ "\n  # expected (=:=): $expected"
                           ~ "\n  #            got: $actual"
            ;
        }
        ok($result, $desc);
    }

    sub is_eq($actual, $expected, str $desc) {
        try {
            my str $a := $actual;
            my str $x := $expected;
            ok($a eq $x, $desc);
            CATCH { ok(0, $desc) }
        }
    }

}


sub diag($msg)                      is export { Testing.diag($msg) }
sub describe($x)                    is export { Testing.describe($x) }
sub plan($nr_of_tests)              is export { Testing.plan($nr_of_tests) }
sub done()                          is export { Testing.done() }
sub ok($condition, $desc?)          is export { Testing.ok($condition, $desc) }
sub fails_ok($block, $desc?)        is export { Testing.fails_ok($block, $desc) }
sub passes_ok($block, $desc?)       is export { Testing.passes_ok($block, $desc) }
sub lives_ok($block, $desc?)        is export { Testing.lives_ok($block, $desc) }
sub dies_ok($block, $desc?)         is export { Testing.dies_ok($block, $desc) }
sub is($actual, $expected, $desc?)  is export { Testing.is($actual, $expected, $desc) }
