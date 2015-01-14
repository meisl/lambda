use v6;
use Test;
use Test::Util;

use Lambda::ListADT;


# module under test:
use Lambda::Streams;

plan 11;


{ # iterate ---------------------------------------------------------------------
    my @calls = @();
    my &f = -> $x {
        my $out = $x * 2;
        @calls.push([$x, $out]);
        $out;
    };

    @calls = @();
    my $xs = $iterate(&f, 1);
    is(@calls.elems, 0, 'nr of calls to f after creating the stream')
        or diag(@calls.perl);

    @calls = @();
    is $car($xs), 1, '1st elem of stream';
    is(@calls.elems, 0, 'nr of calls to f to get 1st elem')
        or diag(@calls.perl);

    @calls = @();
    is $cadr($xs), 2, '2nd elem of stream';
    is(@calls.elems, 1, '1 call to f to get 2nd elem')
        or diag(@calls.perl);

    @calls = @();
    is $caddr($xs), 4, '3rd elem of stream';
    is(@calls.elems, 2, '2 calls to f to get 3rd elem')
        or diag(@calls.perl);

    @calls = @();
    is $cadddr($xs), 8, '4th elem of stream';
    is(@calls.elems, 3, '3 calls to f to get 4th elem')
        or diag(@calls.perl);
    
    @calls = @();
    is $car($cddddr($xs)), 16, '5th elem of stream';
    is(@calls.elems, 4, '4 calls to f to get 5th elem')
        or diag(@calls.perl);
}
