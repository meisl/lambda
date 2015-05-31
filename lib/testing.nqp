#!nqp

use NQPHLL;

#my $test_counter := 0;
my @*TEST_OF_TEST := [];

class Testing {

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
            $out := '"' ~ nqp::escape($x) ~ '" (str)';
        } elsif nqp::isnull($x) {
            $out := 'nqp::null';
        } else {
            if nqp::can($x, 'HOW') && nqp::can($x.HOW, 'name') {
                $out := $x.HOW.name;
            } else {
                $out := nqp::reprname($x);
            }
            $out := $out ~ ', Type object'
                unless nqp::isconcrete($x);
            $out := $out ~ ', invokable'
                if nqp::isinvokable($x);
            $out := (nqp::can($x, 'Str') ?? $x.Str !! '???') ~ " ($out)";
        }
        $out;
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

    method fails_ok($block, $desc) {
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
                $desc := "$desc\n  # should fail but died: '" ~ nqp::escape($error) ~ "'";
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
        my $tc := $test_counter;
        my $depth := +@*TEST_OF_TEST;
        @*TEST_OF_TEST.push('passes_ok');                                       # REFACTOR: "fails_ok" -> "passes_ok"
        $desc := $desc ~ ' passes';                                             # REFACTOR: "fails" -> "passes"
        my $result := NO_VALUE;
        my $error  := NO_VALUE;
        my $inner_returned;
        try {
            $inner_returned := $block();
            CATCH {
                $result := 0;
                $error  := $!;
                $desc := "$desc\n  # should pass but died: '"                   # REFACTOR: "fail" -> "pass"
                    ~ nqp::escape(~$error) ~ "'";
            }
        }
        if $result =:= NO_VALUE { # did not throw
            my $inner_outcome := (+@*TEST_OF_TEST == $depth + 1) && @*TEST_OF_TEST.pop;
            if nqp::ishash($inner_outcome) {
                if !$inner_returned {                                           # REFACTOR: $inner_returned -> !$inner_returned
                    $result := 0;
                    $desc := "$desc\n  # should pass but failed: "              # REFACTOR: "fail but passed" -> "pass but failed"
                           ~ '"' ~ nqp::escape($inner_outcome<output>) ~ '"'
                    ;
                } else {
                    $result := 1;
                }
            } else {
                $result := 0;
                if $tc == $test_counter {
                    $desc := $desc
                        ~ "\n  # should pass but no tests"                      # REFACTOR: "fail" -> "pass"
                        ~ "\n  # returned: '" ~ self.describe($inner_returned)
                    ;
                } else {
                    $desc := $desc
                        ~ "\n  # should pass but broke test-of-test protocol"   # REFACTOR: "fail" -> "pass"
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
                $desc := "$desc\n  # should live but died: '"
                    ~ nqp::escape(~$error) ~ "'";
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
sub ok($condition, $desc?)          is export { Testing.ok($condition, $desc) }
sub fails_ok($block, $desc?)        is export { Testing.fails_ok($block, $desc) }
sub passes_ok($block, $desc?)       is export { Testing.passes_ok($block, $desc) }
sub lives_ok($block, $desc?)        is export { Testing.lives_ok($block, $desc) }
sub dies_ok($block, $desc?)         is export { Testing.dies_ok($block, $desc) }
sub is($actual, $expected, $desc?)  is export { Testing.is($actual, $expected, $desc) }

