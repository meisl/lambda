use v6;
use Test;
use Test::Util;


# module under test:
use Lambda::P6Currying;

plan 20;


sub check_signature($f, Signature:D $s) {
    my @argTypes = $s.params.map(*.type);
    my $retType  = $s.returns;
    my $expectedArity    = @argTypes.elems;
    my $expectedSigElems = @argTypes.elems + 1;
    my $expectedTypeStr  = (@argTypes, $retType).map(*.perl).join(' -> ');

    is $f.arity, $expectedArity, "arity" or diag $f.perl;
    is $f.count, $expectedArity, ".count (==arity)" or diag $f.perl;
    is $f.sig.elems, $expectedSigElems, "nr of elems in sig";
    for 0..$expectedArity - 1 -> $i {
        my $actual   = $f.sig[$i];
        my $expected = @argTypes[$i];
        isa_ok $actual, $expected, "type of param $i (counting from 0): should be {$expected.perl} - and is {$actual.perl}";
    }
    isa_ok $f.sig[*-1], $retType, "type of result: should be {$retType.perl} - and is {$f.sig[*-1].perl}";
    is $f.ty, $expectedTypeStr, "ty(pe) string";
}

sub check_std($f, Signature:D $s) {
    does_ok $f, Callable;
    check_signature($f, $s);
    cmp_ok curry($f), '===', $f, 'currying it again returns the same thing unchanged';
}

{ # invalid signature
    my sub nullarySub { 'bar' };                    # NOT OK    signature: :()
    my $nullaryBlock = { 'baz' };                   # NOT OK    signature: :($_? is parcel)
    my $unaryBlock1 = { ~$_ };                      # NOT OK    signature: :($_? is parcel)
    my $unaryBlock2 = { ~$^a };                     # OK        signature: :($a)                <<< TODO
    my $binaryBlock = { $^a ~ $^b };                # OK        signature: :($a, $b)            <<< TODO
    my $unaryLambdaUnderscore = -> $_ { 'foo' };    # OK        signature: :($_)


    subtest {
        my $g = curry($unaryLambdaUnderscore);
        
        check_std($g, :(Mu -->Mu));
        
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
        check_std($g, :(Str -->Str));
        
        is $g('foo'), 'foo', "can call it with expected nr of args"
            or die;
    }, "curried unary fn {$g.ty}; unapplied";
}


{ # (seemingly) "unary" fn Str -> (Int -> Str)
    my $g = curry(-> Str $x { -> Int $n -->Str{ $x x $n } });
    
    subtest {
        check_std($g, :(Str -->Mu));
    }, "curried unary fn {$g.ty} which returns another unary fn; unapplied";

    subtest({
        is $g('a', 5), 'aaaaa', 'can apply it to all the args at once (aka "overapplying")';

        throws_like { $g('a', 'x') }, X::Typing::ArgBinding, 'over-application with wrongly typed additional args';
        throws_like { $g(7, 9) }, X::Typing::ArgBinding, 'over-application with wrongly typed leading args';
        throws_like { $g(7, 'z') }, X::Typing::ArgBinding, 'over-application with all args wrongly typed';

        throws_like { $g('a', foo => 7) }, X::Typing::UnsupportedNamedArgs, 'over-application with additional *named* args';
        throws_like { $g(bar => 'a', foo => 7) }, X::Typing::UnsupportedNamedArgs, 'over-application with all args *named*';
    }, "curried unary fn {$g.ty} which returns another unary fn; over-applied") or die;

    throws_like { $g(5) }, X::Typing::ArgBinding, 'applying it to wrongly typed arg'
        or die;
    throws_like { $g(x => 'zzz') }, X::Typing::UnsupportedNamedArgs, 'applying it to named arg'
        or die;

    my $h = $g('foo');
    
    subtest({
        check_std($h, :(Int -->Str));
        
        is $h(3), 'foofoofoo', 'can apply it to expected args';
        throws_like { $h('x') }, X::Typing::ArgBinding, 'applying returned fn to with wrongly typed arg';
        throws_like { $h(n => 4) }, X::Typing::UnsupportedNamedArgs, 'applying returned fn to named arg';

    }, "unary fn {$h.ty} returned from curried unary fn {$g.ty}; (the former) unapplied") or die;

}


{ # binary fn Int -> Str -> Str
    my $g ::= curry(-> Int $x, Str $s -->Str{ $s x $x });
    #$g.f does role {
    #    method onPartialApp($self, *@as) {
    #        #exit;
    #    }
    #}

    subtest {
        check_std($g, :(Int, Str -->Str));

        is $g(3, 'x'), 'xxx', "can call it with expected nr of args";
    }, "curried binary fn {$g.ty}; unapplied";

    my $g3 = $g(3);
    subtest {
        check_std($g3, :(Str -->Str)) or die;

        is $g3('y'), 'yyy', "can call it with expected nr of args";
    }, "curried binary fn {$g.ty}; partially applied to \(3)";

    subtest({
        throws_like({$g('x', 5)}, X::Typing::ArgBinding, "passing two args of wrong type to bin fn throws (immediately)");
        throws_like({$g('x')}, X::Typing::ArgBinding, "passing one arg of wrong type to bin fn throws (immediately)");
        throws_like({$g3(5)}, X::Typing::ArgBinding, "passing one more arg of wrong type to partially applied bin fn throws (immediately)");
        
        throws_like({$g(5, 'a', 7)}, X::Typing::Unapplicable, 
            "passing 3rd positional arg: throws X::Unapplicable if bin fn doesn't return another fn");
        throws_like({$g(5, 'a', :foo(7))},  X::Typing::UnsupportedNamedArgs, 
            "passing 3rd named arg: throws 'named args not supported'");

        throws_like({$g3('b', 7)}, X::Typing::Unapplicable, 
            "passing two args to partially applied bin fn: throws X::Unapplicable if bin fn doesn't return another fn");
        
        throws_like({$g3(9, 6)}, X::Typing::ArgBinding, 
            "passing two args (1st of wrong type) to partially applied bin fn throws X::ArgBinding");
    }, "curried binary fn {$g.ty}; invalid calls") or die;
}


{ # (seemingly) "binary" fn  Int -> Str -> (Int -> Str)
    my @seen = @();

    my $g ::= curry(
        -> Int $a0, Str $a1 {
            -> Int $a2 -->Str{ 
                @seen.push(($a0, $a1, $a2).tree); "@ call {@seen.elems}: (" ~ @seen[*-1].map(*.perl).join(', ') ~ ")" 
            }
        }
    );
    
    subtest {
        check_std($g, :(Int, Str -->Mu)) or die;

        is $g(5, 'a', 74), '@ call 1: (5, "a", 74)', 'can apply it to all args at once (aka "overapplying")' or die;
    }, 'curried binary fn ' ~ $g.ty ~ ' which returns a unary fn; unapplied' or die;

    subtest({
        throws_like { $g('x') }, X::Typing::ArgBinding, 'partial app with wrongly typed arg';
        throws_like { $g(:x(3)) }, X::Typing::UnsupportedNamedArgs, 'partial app with named arg';

        throws_like { $g(6, 7) }, X::Typing::ArgBinding, 'complete app with wrongly typed 2nd arg';
        throws_like { $g(6, :x<yyy>) }, X::Typing::UnsupportedNamedArgs, 'complete app with named arg';

        throws_like { $g('u', 'z', 6) }, X::Typing::ArgBinding, 'over-app with wrongly typed 1st arg';
        throws_like { $g(6, 7, 8) }, X::Typing::ArgBinding, 'over-app with wrongly typed 2nd arg';
        throws_like { $g(6, 'z', 'w') }, X::Typing::ArgBinding, 'over-app with wrongly typed 3rd arg';

        throws_like { $g(6, 'z', :x<yyy>) }, X::Typing::UnsupportedNamedArgs, 'over-app app with named arg';
        throws_like { $g(6, 'z', 7, :x<yyy>) }, X::Typing::UnsupportedNamedArgs, 'over-app app with *additional* named arg';

    }, 'curried binary fn ' ~ $g.ty ~ ' which returns a unary fn; invalid calls') or die;

    my $g1 = $g(1);
    subtest {
        check_std($g1, :(Str -->Mu)) or die;

        is $g1('b', 9), '@ call 2: (1, "b", 9)', 'can apply it to all the args at once (aka "overapplying")' or die;
    }, 'curried binary fn ' ~ $g.ty ~ ' which returns a unary fn; partially applied to \(1)' or die;

    my $g1_two = $g1("two");
    subtest {
        check_std($g1_two, :(Int -->Str)) or die;

        is $g1_two(23), '@ call 3: (1, "two", 23)', 'can apply it to the args expected by the returned fn")' or die;
    }, 'curried binary fn ' ~ $g.ty ~ ' which returns a unary fn; partially applied to \(1), then to \("two")' or die;
}


{ # ternary fn Int -> Str -> Int -> Str
    my @seen = @();

    my $g ::= curry(
        -> Int $a0, Str $a1, Int $a2 -->Str{ 
            @seen.push(($a0, $a1, $a2).tree); "@ call {@seen.elems}: (" ~ @seen[*-1].map(*.perl).join(', ') ~ ")" 
        }
    );
    
    subtest {
        check_std($g, :(Int, Str, Int -->Str)) or die;
    }, "curried ternary fn; unapplied";

    #say $g(1, "two", 3);
    #say $g(2, "three", 4);

    my $g1 = $g(1);
    subtest {
        check_std($g1, :(Str, Int -->Str)) or die;
    }, 'ternary fn; partially applied to \(1)';

    my $g1_two = $g1("two");
    subtest {
        check_std($g1_two, :(Int -->Str)) or die;
    }, 'ternary fn; partially applied to \(1), then to \("two")';

    my $g1two = $g(1, "two");
    subtest {
        check_std($g1two, :(Int -->Str)) or die;
    }, 'ternary fn; partially applied to \(1, "two")';

}
