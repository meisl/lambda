use v6;

use Test;
use Test::Util;
use Lambda::Base;
use Lambda::Boolean;    # TODO: move findFP (tests) out of Base.pm6, st. dependency on Boolean.pm6 is made clear

plan 52;

{ # lambdaFn
    my $omega ::= lambdaFn( 'ω', 'λx.x x', -> &x { &x(&x) } );
   is_properLambdaFn($omega);
}

{ # id, aka I
    is_properLambdaFn $id;
    ok $I === $id, '$I is a synonym for $id';

    is $id("x"), "x", 'id("x")';
    is $id(5), 5, 'id(5)';
    is $id($id), $id, 'id(id)';
}

{ # const, aka K
    is_properLambdaFn $const;
    ok $K === $const, '$K is a synonym for $const';

    is $const('x')(5),  'x',        'const("x")(5)';
    is $const(5)(23),   5,          'const(5)(23)';
    is $const(42).Str,  '(λy.42)',  'const(42).Str';
    is $const($id)(23), $id,        'const(id)(23)';
    is $const($id).Str, "(λy.$id)", 'const($id).Str';

    #is $const("x", 5), "x", 'const("x", 5)';
    #is $const(5, 23), 5, 'const(5, 23)';
    #is $const($id, 23), $id, 'const(id, 23)';

}

{ # compose, aka B
    is_properLambdaFn $B;
    ok $compose === $B, '$compose is a synonym for $B';

    my @seen = @();
    subtest({
        my $f = -> Int:D $i { @seen.push($i.perl); ($i * 2).Str.perl } does Definition(:symbol<f>);
        my $g = -> Str:D $s { @seen.push($s.perl); $s.Int - 23       } does Definition(:symbol<g>);

        my $h = $B($f, $g);
        does_ok     $h, lambda,     'B f g';
        doesnt_ok   $h, Definition, 'B f g';

        my $result = $h('42');
        is @seen[0], '"42"', '((B f g) "42"): arg was passed to g first';
        is @seen[1], 19,     '((B f g) "42"): result of g applied to arg was passed to f';
        is $result, '"38"',  '((B f g) "42"): overall result is that of f';
    }, "compose aka B") or diag 'seen: [ ' ~  @seen.map(*.perl).join(', ') ~ ' ]' and die; 
}

{ # swap-args, aka C
    is_properLambdaFn $C;
    ok $swap-args === $C, '$swap-args is a synonym for $C';

    my @seen = @();
    subtest({
        my $f = -> $a, $b { @seen.push([$a, $b]) } does Definition(:symbol<f>);

        my $g = $C($f);
        does_ok     $g, lambda,     'C f';
        doesnt_ok   $g, Definition, 'C f';

        $g('a', 'b');
        is @seen[0][0], 'b', '((C f) a b): 2nd arg was passed first';
        is @seen[0][1], 'a', '((C f) a b): 1st arg was passed second';
        
        my $h = $C($g);
        does_ok     $h, lambda,     'C (C f)';
        doesnt_ok   $h, Definition, 'C (C f)';

        $h(42, 23);
        is @seen[1][0], 42, '(((C (C f)) 42 23): 1st arg was passed fist';
        is @seen[1][1], 23, '(((C (C f)) 42 23): 2nd arg was passed second';
    }, "swapargs aka C") or diag 'seen: [ ' ~  @seen.map(*.perl).join(', ') ~ ' ]' and die; 
}

{ # double-arg, aka W
    is_properLambdaFn $W;
    ok $double-arg === $W, '$double-arg is a synonym for W';

    my @seen = @();
    subtest({
        my $f = -> $a, $b { @seen.push([$a, $b]) } does Definition(:symbol<f>);
        $f does lambda('λa.λb.#true');

        my $g = $W($f);
        does_ok     $g, lambda,     'W f';
        doesnt_ok   $g, Definition, 'W f';

        $g('a');
        is @seen.elems,     1, '((W f) a): original f got called once';
        is @seen[0].elems,  2, '((W f) a): original f got called with two arguments';
        is @seen[0][0], 'a', '((W f) a): original arg was passed as 1st arg';
        is @seen[0][1], 'a', '((W f) a): original arg was passed as 2nd arg';

    }, "double-arg aka W") or diag 'seen: [ ' ~  @seen.map(*.perl).join(', ') ~ ' ]' and die; 
}

{ # Y combinator
    is_properLambdaFn $Y;
}

{ # Y combinator for unary f
    my $fact-stub = lambdaFn(
        'fact', 'λself.λn.if (zero? n) 1 (* n (self (- n 1)))',
        -> &self {
            -> Int $n {
                $n == 0 ?? 1 !! $n * &self($n - 1)
            }
        }
    );
    my $fact = $Y($fact-stub);
    does_ok $fact, lambda, '(Y f)';
    does_ok $fact, Definition, '(Y f)';
    is $fact.symbol, $fact-stub.symbol, "Y uses stub's .symbol (if any) as Definition symbol of result";

    does_ok $Y(-> &self { &self }), lambda, '(Y g) where g does not role "lambda" - itself';
    doesnt_ok $Y(lambdaFn(Str, 'λfoo."bar"', -> &self { -> $foo { 'bar' } } )), Definition,
        "Y doesn't make its result a Definition if stub doesnt Definition";

    subtest {
        is $fact(0),   1, '0! =   1';
        is $fact(1),   1, '1! =   1';
        is $fact(2),   2, '2! =   2';
        is $fact(3),   6, '3! =   6';
        is $fact(4),  24, '4! =  24';
        is $fact(5), 120, '5! = 120';
        is $fact(6), 720, '5! = 720';
        is $fact(7),5040, '5! =5040';
    }, 'Y combinator for unary f; ex. factorial: ' ~ $fact.lambda;
}

{ # Y combinator for binary f
    my $ackPeter = $Y( lambdaFn(
        'ackPeter', 'λself.λa.λb.(if (zero? a) (succ b) (if (zero? b) (self (pred a) 1) (self (pred a) (self a (pred b)))))',
        -> &self {
            -> Int $a, $b {
                if $a == 0 {
                    $b + 1;
                } elsif $b == 0 {
                    &self($a - 1, 1);
                } else {
                    &self($a - 1, &self($a, $b - 1));
                }
            }
        }
    ));

    subtest {
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

        ## Attention: becoming really slow soon:

        #is $ackPeter(3, 5), 8*2**5-3, 'ap(3, 5) = ' ~ (8*2**5-3);
        #is $ackPeter(3, 6), 8*2**6-3, 'ap(3, 6) = ' ~ (8*2**6-3);
        #is $ackPeter(3, 7), 8*2**7-3, 'ap(3, 7) = ' ~ (8*2**7-3);

        is $ackPeter(4, 0),    13, 'ap(4, 0) =     13';
        #is $ackPeter(4, 1), 65533, 'ap(4, 1) =  65533';
    }, 'Y combinator for binary f; ex. Ackermann-Péter: ' ~ $ackPeter.lambda;
}

# fixed-point search ----------------------------------------------------------


{ # findFP
   is_properLambdaFn($findFP);

    my $predicate;
    my $function;
    my $actual;
    my @seen;
    my $values;

    $predicate = -> $x, $y {
        ($x === $y) ?? $true !! $false
    };

    $function = $K(42);
    $actual = $findFP($predicate, $function, 23); # just *some* start value different from any in @values
    is($actual, 42, "findFP with === finds fixed-point of K");

    $values = @(1, 3, '3', 2, 5, 5, 7);
    @seen = @();
    $function = -> $x {
        my $out = $values[@seen.elems];
        @seen.push($x);
        diag ">>>> f({$x.perl}), returning {$out.perl}";
        $out;
    };

    $actual = $findFP($predicate, $function, 23); # just *some* start value different from any in @values
    is($actual, 5, "findFP with === finds fixed-point in \"enumerate\"(1, 3, '3', 2, 5, 5, 7)");


    $predicate = -> $x, $y {
        ($y === 7) ?? $true !! $false
    };

    @seen = @();
    $actual = $findFP($predicate, $function, 23); # just *some* start value different from any in @values
    is($actual, 5, "findFP with (y === 7) on \"enumerate\"(1, 3, '3', 2, 5, 5, 7) returns 1st arg to predicate rather than 2nd")
        or diag("seen: {@seen.perl}") and die;
}


# projections -----------------------------------------------------------------

{ # projections of 2
    is_properLambdaFn $pi1o2;
    is_properLambdaFn $pi2o2;

    is $pi1o2(23, 42), 23, 'π2->1 returns 1st arg';
    is $pi2o2(23, 42), 42, 'π2->2 returns 2nd arg';
}

{ # projections of 3
    is_properLambdaFn $pi1o3;
    is_properLambdaFn $pi2o3;
    is_properLambdaFn $pi3o3;

    is $pi1o3(23, 42, 4711),   23, 'π3->1 returns 1st arg';
    is $pi2o3(23, 42, 4711),   42, 'π3->2 returns 2nd arg';
    is $pi3o3(23, 42, 4711), 4711, 'π3->3 returns 3rd arg';
}

{ # projections of 4
    is_properLambdaFn $pi1o4;
    is_properLambdaFn $pi2o4;
    is_properLambdaFn $pi3o4;
    is_properLambdaFn $pi4o4;

    is $pi1o4(23, 42, 4711, "foo"),    23, 'π4->1 returns 1st arg';
    is $pi2o4(23, 42, 4711, "foo"),    42, 'π4->2 returns 2nd arg';
    is $pi3o4(23, 42, 4711, "foo"),  4711, 'π4->3 returns 3rd arg';
    is $pi4o4(23, 42, 4711, "foo"), "foo", 'π4->4 returns 4th arg';
}
