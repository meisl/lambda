#!nqp
use testing;
use Util;

use Backtrace;

plan(7);

my $trace := Backtrace.new;

ok(istype($trace, Backtrace), "Backtrace.new returns a Backtrace");
is(describe($trace), '(Backtrace)', 'concrete obj');

ok(nqp::islist($trace.list), "Backtrace's .list returns a list");

my $frame;
lives_ok({ $frame := $trace[0] }, 'Backtrace supports positional access');
is(describe($frame), '(Frame)', 'Backtrace contains Frames');

my $trace2;
lives_ok({ $trace2 := $trace.filter }, "Backtrace's .filter...");
ok(istype($trace2, Backtrace), "...returns another Backtrace")
    || diag($trace2);


#diag($trace.Str);

done();
