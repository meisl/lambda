use v6;

use Test;
use Lambda::Base;
use Lambda::MethodFixedPoint;

plan 2;

subtest({ # iteratedApp
    my $values = (@(1, 3, '3', 2, 5, 5, 23, 42) does MethodFixedPoint) does role {
        my $n = 0;
        my sub f($whatever) {
            my $out = $values[$n++];
            diag ">>>> f({$whatever.perl}), returning {$out.perl}";
            $out;
        }
        method go { 
            self.iteratedApp(&f, * === *, $id) 
        }
    };

    my $actual = $values.go;
    cmp_ok($actual[0], '===', $id, 'includes specified $start value as first')
        or diag "got sequence $actual";
    is($actual[1], 1, '1st return value')
        or diag "got sequence $actual";
    is($actual[2], 3, '2nd return value')
        or diag "got sequence $actual";
    is($actual[2], '3', '3rd return value')
        or diag "got sequence $actual";
    is($actual[4], 2, '4th return value')
        or diag "got sequence $actual";
    is($actual[5], 5, '5th return value')
        or diag "got sequence $actual";
    is($actual[6], 5, '6th return value, same as 5th')
        or diag "got sequence $actual";
    is($actual.elems, 7, "ends with fixed-point, listed twice")
        or diag "got sequence $actual";
}, 'iteratedApp');


subtest({ # mfp
    my $values = (@(1, 3, '3', 2, 5, 5) does MethodFixedPoint) does role {
        my $n = 0;
        my sub f($whatever) {
            my $out = $values[$n++];
            diag ">>>> f({$whatever.perl}), returning {$out.perl}";
            $out;
        }
        method go { 
            self.mfp(&f, * === *, $id) 
        }
    };

    my $actual = $values.go;
    is($actual, 5, "mfp finds fixed-point");
}, "mfp");