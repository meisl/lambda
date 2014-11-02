use v6;

use Test;
use Test::Util;
use Lambda::Boolean;

use Lambda::MaybeADT;

plan 5;


{ # Maybe->valueWithDefault
   is_properLambdaFn($Maybe2valueWithDefault);

    is $Maybe2valueWithDefault.symbol, 'Maybe->valueWithDefault', '$Maybe2valueWithDefault.symbol';
    is $Maybe2valueWithDefault.Str,    'Maybe->valueWithDefault', '$Maybe2valueWithDefault.Str';

    my $m;

    $m = $None;
    is $Maybe2valueWithDefault($m, 42), 42, "(Maybe->valueWithDefault $m 42)";

    $m = $Some(23);
    is $Maybe2valueWithDefault($m, 42), 23, "(Maybe->valueWithDefault $m 42)";
}
