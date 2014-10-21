use v6;

use Test;
use Test::Util;
use Lambda::Base;

plan 51;

{
    dies_ok { $id   = 0 },    '$id is immutable';
    does_ok   $id,  lambda,   '$id';
    does_ok   $id,  name,     '$id';

    dies_ok { $const  = 0 },  '$const is immutable';
    does_ok   $const, lambda, '$const';
    does_ok   $const, name,   '$const';

    dies_ok { $swap-args  = 0 },  '$swap-args is immutable';
    does_ok   $swap-args, lambda, '$swap-args';
    does_ok   $swap-args, name,   '$swap-args';

    ok $C === $swap-args, '$C is a synonym for swap-args';

    dies_ok { $Y      = 0 },  '$Y is immutable';
    does_ok   $Y,     lambda, '$Y';
    does_ok   $Y,     name,   '$Y';
}

{
    is $id("x"), "x", 'id("x")';
    is $id(5), 5, 'id(5)';
    is $id($id), $id, 'id(id)';
}

{
    is $const('x')(5),  'x',        'const("x")(5)';
    is $const(5)(23),   5,          'const(5)(23)';
    is $const(42).Str,  '(λy.42)',  'const(42).Str';
    is $const($id)(23), $id,        'const(id)(23)';
    is $const($id).Str, "(λy.$id)", 'const($id).Str';
}

{ # swap-args, aka C
    my @seen = @();
    subtest({
        my $f = -> $a, $b { @seen.push([$a, $b]) } does name('f');

        my $g = $C($f);
        does_ok $g, lambda, 'C f';
        does_ok $g, name,   'C f';

        $g('a', 'b');
        is @seen[0][0], 'b', '((C f) a b): 2nd arg was passed first';
        is @seen[0][1], 'a', '((C f) a b): 1st arg was passed second';
        
        my $h = $C($g);
        does_ok $h, lambda, 'C (C f)';
        does_ok $h, name,   'C (C f)';

        $h(42, 23);
        is @seen[1][0], 42, '(((C (C f)) 42 23): 1st arg was passed fist';
        is @seen[1][1], 23, '(((C (C f)) 42 23): 2nd arg was passed second';
    }, "swapargs aka C") or diag 'seen: [ ' ~  @seen.map(*.perl).join(', ') ~ ' ]' and die; 
}

{ # Y combinator for unary f
    my $fact = lambdaFn(
        'fact', 'Y λself.λn.if (zero? n) 1 (* n (self (- n 1)))',
        $Y(-> $self {
            -> Int $n {
                $n == 0 ?? 1 !! $n * $self($n - 1)
            }
        })
    );
    diag 'Y combinator for unary f; ex. factorial: ' ~ $fact.lambda;

    is $fact(0),   1, '0! =   1';
    is $fact(1),   1, '1! =   1';
    is $fact(2),   2, '2! =   2';
    is $fact(3),   6, '3! =   6';
    is $fact(4),  24, '4! =  24';
    is $fact(5), 120, '5! = 120';
    is $fact(6), 720, '5! = 720';
}

{ # Y combinator for binary f
    my $ackPeter = lambdaFn(
        'ackPeter', 'Y λself.λa.λb.???',
        $Y(-> $self {
            -> Int $a, $b {
                if $a == 0 {
                    $b + 1;
                } elsif $b == 0 {
                    $self($a - 1, 1);
                } else {
                    $self($a - 1, $self($a, $b - 1));
                }
            }
        })
    );
    diag 'Y combinator for binary f; ex. Ackermann-Péter: ' ~ $ackPeter.lambda;

    # base case:
    is $ackPeter(0, 0),   1, 'ap(0, 0) =   1';
    is $ackPeter(0, 1),   2, 'ap(0, 1) =   2';
    is $ackPeter(0, 2),   3, 'ap(0, 2) =   3';
    is $ackPeter(0, 3),   4, 'ap(0, 3) =   4';
    is $ackPeter(0, 4),   5, 'ap(0, 4) =   5';

    # recursive cases:
    is $ackPeter(1, 0),   2, 'ap(1, 0) =   2';
    is $ackPeter(1, 1),   3, 'ap(2, 1) =   3';
    is $ackPeter(1, 2),   4, 'ap(3, 2) =   4';
    is $ackPeter(1, 3),   5, 'ap(4, 3) =   5';
    is $ackPeter(1, 4),   6, 'ap(5, 4) =   6';

    is $ackPeter(2, 0),   3, 'ap(2, 0) =   3';
    is $ackPeter(2, 1),   5, 'ap(2, 1) =   5';
    is $ackPeter(2, 2),   7, 'ap(2, 2) =   7';
    is $ackPeter(2, 3),   9, 'ap(2, 3) =   9';
    is $ackPeter(2, 4),  11, 'ap(2, 4) =  11';

    is $ackPeter(3, 0),   5, 'ap(3, 0) =   5';
    is $ackPeter(3, 1),  13, 'ap(3, 1) =  13';
    is $ackPeter(3, 2),  29, 'ap(3, 2) =  29';
    is $ackPeter(3, 3),  61, 'ap(3, 3) =  61';
    is $ackPeter(3, 4), 125, 'ap(3, 4) = 125';

    # attention, becoming really slow soon:
    skip {
        is $ackPeter(3, 5), 8*2**5-3, 'ap(3, 5) = ' ~ (8*2**5-3);
        is $ackPeter(3, 6), 8*2**6-3, 'ap(3, 6) = ' ~ (8*2**6-3);
        is $ackPeter(3, 7), 8*2**7-3, 'ap(3, 7) = ' ~ (8*2**7-3);
    }

    is $ackPeter(4, 0),    13, 'ap(4, 0) =     13';
    #is $ackPeter(4, 1), 65533, 'ap(4, 1) =  65533';
}

{
    #is $const("x", 5), "x", 'const("x", 5)';
    #is $const(5, 23), 5, 'const(5, 23)';
    #is $const($id, 23), $id, 'const(id, 23)';
}
