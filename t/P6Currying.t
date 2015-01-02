use v6;

use Test;
use Test::Util;

use Lambda::P6Currying;


plan 19;

{ # invalid signature
    my sub nullarySub { 'bar' };                    # NOT OK    signature: :()
    my $nullaryBlock = { 'baz' };                   # NOT OK    signature: :($_? is parcel)
    my $unaryBlock1 = { ~$_ };                      # NOT OK    signature: :($_? is parcel)
    my $unaryBlock2 = { ~$^a };                     # OK        signature: :($a)                <<< TODO
    my $binaryBlock = { $^a ~ $^b };                # OK        signature: :($a, $b)            <<< TODO
    my $unaryLambdaUnderscore = -> $_ { 'foo' };    # OK        signature: :($_)


    subtest {
        my $g = curry($unaryLambdaUnderscore);
        does_ok $g, Callable;

        is $g.arity, 1, "arity";
        is $g.count, 1, ".count (==arity)";
        is $g.sig.elems, 2, "nr of elems in sig";
        isa_ok $g.sig[0], Mu, "type of 1st param";
        isa_ok $g.sig[1], Mu, "type of result";
        is $g.ty, 'Mu -> Mu', "ty(pe) string";
        
        cmp_ok curry($g), '===', $g, 'currying it again returns the same thing unchanged';
        
        is $g(Mu), 'foo', "can call it with expected nr of args";
    }, 'currying unary lambda where param is named "$_"';

    subtest {
        dies_ok({curry($nullaryBlock)}, 'nullary block');
        dies_ok({curry($unaryBlock1)}, 'block using $_');
    }, 'nullary block or block using $_: cannot curry...';

    subtest {
        # nullary fn
        dies_ok({curry(&nullarySub)}, 'nullary sub');
        dies_ok({curry(-> { 'foo' })}, 'nullary lambda expr (aka "pointy block")');

        # optional params
        dies_ok({curry(-> $y, $x? {'bar'})}, "lambda expr with optional (positional) params");
        dies_ok({curry(-> $y, :$x {'bar'})}, "lambda expr with optional (named) params");

        # named params
        dies_ok({curry(-> :$x! {'bar'})}, "lambda expr with (mandatory) named params");
        dies_ok({curry(-> $y, :$x! {'bar'})}, "lambda expr with (mandatory) named params");
        
        # slurpy params
        dies_ok({curry(-> $y, *@x {'bar'})}, "lambda expr with slurpy (positional) params");
        
        # capture param
        dies_ok({curry(-> $y, |x {'bar'})}, "lambda expr with capture param");
        
        # parcel param
        dies_ok({curry(-> \x {'bar'})}, "lambda expr with parcel param");
    }, 'sub and lambda: cannot curry...';
}


{ # unary fn Str -> Str
    my $g = curry(-> Str $x -->Str{ $x });
    
    subtest {
        does_ok $g, Callable;

        is $g.arity, 1, "arity";
        is $g.count, 1, ".count (==arity)";
        is $g.sig.elems, 2, "nr of elems in sig";
        isa_ok $g.sig[0], Str, "type of 1st param";
        isa_ok $g.sig[1], Str, "type of result";
        is $g.ty, 'Str -> Str', "ty(pe) string";
        
        cmp_ok curry($g), '===', $g, 'currying it again returns the same thing unchanged';
        
        is $g('foo'), 'foo', "can call it with expected nr of args";
    }, "curried unary fn {$g.ty}; unapplied";
}


{ # unary fn Str -> (Int -> Str)
    my $g = curry(-> Str $x { -> Int $n -->Str{ $x x $n } });
    
    subtest {
        does_ok $g, Callable;

        is $g.arity, 1, "arity";
        is $g.count, 1, ".count (==arity)";
        is $g.sig.elems, 2, "nr of elems in sig";
        isa_ok $g.sig[0], Str, "type of 1st param";
        isa_ok $g.sig[1], Mu, "type of result";
        is $g.ty, 'Str -> Mu', "ty(pe) string";
        
        cmp_ok curry($g), '===', $g, 'currying it again returns the same thing unchanged';
        
        is $g('a', 5), 'aaaaa', 'can apply it to all the args at once';
    }, "curried unary fn {$g.ty} which returns another unary fn; unapplied";

    my $h = $g('foo');
    
    subtest {
        does_ok $h, Callable;

        is $h.arity, 1, "arity";
        is $h.count, 1, ".count (==arity)";
        is $h.sig.elems, 2, "nr of elems in sig";
        isa_ok $h.sig[0], Int, "type of 1st param";
        isa_ok $h.sig[1], Str, "type of result";
        is $h.ty, 'Int -> Str', "ty(pe) string";
        
        cmp_ok curry($h), '===', $h, 'currying it again returns the same thing unchanged';
        
        is $h(3), 'foofoofoo', 'can apply it to expected args';
    }, "unary fn {$h.ty} returned from curried unary fn {$g.ty}; (the former) unapplied";

}


{ # binary fn
    my $g ::= curry(-> Int $x, Str $s -->Str{ $s x $x });
    $g.f does role {
        method onPartialApp($self, *@as) {
            #exit;
        }
    }

    subtest {
        does_ok $g, Callable;

        is $g.arity, 2, "arity";
        is $g.count, 2, ".count (==arity)";
        is $g.sig.elems, 3, "nr of elems in sig";
        isa_ok $g.sig[0], Int, "type of 1st param";
        isa_ok $g.sig[1], Str, "type of 2nd param";
        isa_ok $g.sig[2], Str, "type of result";
        is $g.ty, 'Int -> Str -> Str', "ty(pe) string";
        
        cmp_ok curry($g), '===', $g, 'currying it again returns the same thing unchanged';

        is $g(3, 'x'), 'xxx', "can call it with expected nr of args";
    }, "curried binary fn {$g.ty}; unapplied";

    my $g3 = $g(3);
    subtest {
        does_ok $g3, Callable;

        is $g3.arity, 1, "arity";
        is $g3.count, 1, ".count (==arity)";
        is $g3.sig.elems, 2, "nr of elems in sig";
        isa_ok $g3.sig[0], Str, "type of 1st param";
        isa_ok $g3.sig[1], Str, "type of result";
        is $g3.ty, 'Str -> Str', "ty(pe) string";
        
        cmp_ok curry($g3), '===', $g3, 'currying it again returns the same thing unchanged';

        is $g3('y'), 'yyy', "can call it with expected nr of args";
    }, "curried binary fn {$g.ty}; partially applied to \(3)";


    dies_ok({$g('x', 5)}, "passing two args of wrong type to bin fn throws (immediately)");
    dies_ok({$g('x')}, "passing one arg of wrong type to bin fn throws (immediately)");
    dies_ok({$g3(5)}, "passing one more arg of wrong type to partially applied bin fn throws (immediately)");

    throws_like({$g(5, 'a', 7)}, X::Typing::Unapplicable, 
        "passing 3rd positional arg: throws X::Unapplicable if bin fn doesn't return another fn");
    throws_like({$g(5, 'a', :foo(7))},  X::Typing::UnsupportedNamedArgs, 
        "passing 3rd named arg: throws 'named args not supported'");

    throws_like({$g3('b', 7)}, X::Typing::Unapplicable, 
        "passing two args to partially applied bin fn: throws X::Unapplicable if bin fn doesn't return another fn");
    
    throws_like({$g3(9, 6)}, X::Typing::ArgBinding, 
        "passing two args (1st of wrong type) to partially applied bin fn throws X::ArgBinding");
}


{ # ternary fn
    my @seen = @();

    my $g ::= curry(-> Int $a0, Str $a1, Int $a2 -->Str{ @seen.push(($a0, $a1, $a2).tree); "@ call {@seen.elems}: (" ~ @seen[*-1].map(*.perl).join(', ') ~ ")" });
    
    subtest {
        does_ok $g, Callable;

        is $g.arity, 3, "arity";
        is $g.count, 3, ".count (==arity)";
        is $g.sig.elems, 4, "nr of elems in sig";
        isa_ok $g.sig[0], Int, "type of 1st param";
        isa_ok $g.sig[1], Str, "type of 2nd param";
        isa_ok $g.sig[2], Int, "type of 3rd param";
        isa_ok $g.sig[3], Str, "type of result";
        is $g.ty, 'Int -> Str -> Int -> Str', "ty(pe) string";
        
        cmp_ok curry($g), '===', $g, 'currying it again returns the same thing unchanged';
    }, "curried ternary fn; unapplied";

    #say $g(1, "two", 3);
    #say $g(2, "three", 4);

    my $g1 = $g(1);
    subtest {
        is $g1.arity, 2, "arity";
        is $g1.count, 2, ".count (==arity)";
        is $g1.sig.elems, 3, "nr of elems in sig";
        isa_ok $g1.sig[0], Str, "type of 1st param";
        isa_ok $g1.sig[1], Int, "type of 2nd param";
        isa_ok $g1.sig[2], Str, "type of result";
        is $g1.ty, 'Str -> Int -> Str', "ty(pe) string";
        
        cmp_ok curry($g1), '===', $g1, 'currying it again returns the same thing unchanged';
    }, 'ternary fn; partially applied to \(1)';

    my $g1_two = $g1("two");
    subtest {
        is $g1_two.arity, 1, "arity";
        is $g1_two.count, 1, ".count (==arity)";
        is $g1_two.sig.elems, 2, "nr of elems in sig";
        isa_ok $g1_two.sig[0], Int, "type of 1st param";
        isa_ok $g1_two.sig[1], Str, "type of result";
        is $g1_two.ty, 'Int -> Str', "ty(pe) string";
        
        cmp_ok curry($g1_two), '===', $g1_two, 'currying it again returns the same thing unchanged';
    }, 'ternary fn; partially applied to \(1), then to \("two")';

    my $g1two = $g(1, "two");
    subtest {
        is $g1two.arity, 1, "arity";
        is $g1two.count, 1, ".count (==arity)";
        is $g1two.sig.elems, 2, "nr of elems in sig";
        isa_ok $g1two.sig[0], Int, "type of 1st param";
        isa_ok $g1two.sig[1], Str, "type of result";
        is $g1two.ty, 'Int -> Str', "ty(pe) string";
        
        cmp_ok curry($g1two), '===', $g1two, 'currying it again returns the same thing unchanged';
    }, 'ternary fn; partially applied to \(1, "two")';

}
