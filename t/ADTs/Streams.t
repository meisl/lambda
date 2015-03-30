use v6;
use Test;
use Test::Util;

use Lambda::ListADT;


# module under test:
use Lambda::Streams;

plan 14;


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

{ # lazy map --------------------------------------------------------------------
    my $plus1 = -> Int $n { $n + 1 };
    my $times2 = -> Int $n { $n * 2 };

    my $nats = $iterate($plus1, 0);
    subtest({
        is $car($nats), 0, '(iterate (+ 1) 0) = [*0*, 1, 2, 3, ...]';
        is $cadr($nats), 1, '(iterate (+ 1) 0) = [0, *1*, 2, 3, ...]';
        is $caddr($nats), 2, '(iterate (+ 1) 0) = [0, 1, *2*, 3, ...]';
        is $cadddr($nats), 3, '(iterate (+ 1) 0) = [0, 1, 2, *3*, ...]';
    }, 'nats = (iterate (+ 1) 0) = [0, 1, 2, 3, ...]');

    my $even = $map-lazy($times2, $nats);
    subtest({
        is $car($even), 0, '(map-lazy (* 2) nats) = [*0*, 2, 4, 6, ...]';
        is $cadr($even), 2, '(map-lazy (* 2) nats) = [0, *2*, 4, 6, ...]';
        is $caddr($even), 4, '(map-lazy (* 2) nats) = [0, 2, *4*, 6, ...]';
        is $cadddr($even), 6, '(map-lazy (* 2) nats) = [0, 2, 4, *6*, ...]';
    }, 'even = (map-lazy (* 2) nats) = [0, 2, 4, 6, ...]');

    my $odd = $map-lazy($plus1, $even);
    subtest({
        is $car($odd), 1, '(map-lazy (+ 1) even) = [*1*, 3, 5, 7, ...]';
        is $cadr($odd), 3, '(map-lazy (+ 1) even) = [1, *3*, 5, 7, ...]';
        is $caddr($odd), 5, '(map-lazy (+ 1) even) = [1, 3, *5*, 7, ...]';
        is $cadddr($odd), 7, '(map-lazy (+ 1) even) = [1, 3, 5, *7*, ...]';
    }, 'odd = (map-lazy (+ 1) (map-lazy (* 2) nats)) = [0, 2, 4, 6, ...]');
}
