use v6;
use Test;
use Test::Util;

use Lambda::BaseP6;

# module under test:
use Lambda::ADT_auto;

plan 39;


# prep ------------------------------------------------------------------------

# a sample ADT
role Foo does ADT {
    my $repr = ADTRepr.new(Foo,
        FooCtor1of3 => 0,
        FooCtor2of3 => 1,
        FooCtor3of3 => 2
    );
    method repr { $repr }
}


my $FooCtor1o3 = lambdaFn( 'FooCtor1o3', 'λclient.client', -> $client { $client }) does Foo;
my $FooCtor2o3 = lambdaFn( 'FooCtor2o3', 'λa.λclient.client a',
    -> $a {
        -> $client { $client($a) } does Foo
    }
);
my $FooCtor3o3 = lambdaFn( 'FooCtor3o3', 'λa.λb.λclient.client a b',
    -> $a, $b {
        -> $client { $client($a, $b) } does Foo
    }
);

my $fooInstance1o3 = $FooCtor1o3;   # 0-arity ctor is itself an instance
my $fooInstance2o3 = $FooCtor2o3(23);
my $fooInstance3o3 = $FooCtor3o3(23, 42);

my $fooInstance = $fooInstance1o3;


# another sample ADT
role Bar does ADT {
    my $repr = ADTRepr.new(Bar,
        BarCtor1of3 => 0,
        BarCtor2of3 => 1,
        BarCtor3of3 => 2
    );
    method repr { $repr }
}
my $barInstance = lambdaFn( 'aBar', 'λNYI."not yet implemented', -> $client { $client }) does Bar;


{ # ADTRepr
    my $repr;
    
    dies_ok { ADTRepr.new }, 'ADTRepr.new with no args';
    dies_ok { ADTRepr.new(Blah => 5) }, 'ADTRepr.new with no positional args (no typeName)';
    dies_ok { ADTRepr.new(Foo) }, 'ADTRepr.new with no named args (no constructor specs)';
    dies_ok { ADTRepr.new('Foo', Blah => 5) }, 'ADTRepr.new with Str for the type';
    dies_ok { ADTRepr.new(Int, Blah => 5) }, 'ADTRepr.new with non-ADT type as 1st arg';
    #dies_ok { ADTRepr.new(ADT, Blah => 5) }, 'ADTRepr.new with type ADT as 1st arg';

    $repr = Foo.repr;

    does_ok $repr, ADTRepr, 'Foo.repr';

    is $repr.name, 'Foo', '.repr.name';
    is $repr.ctors.elems, 3, '.repr.ctors.elems'
        or diag $repr.ctors.perl;
    is substr($repr.perl, 0, 15), 'ADTRepr.new(Foo', '.repr.perl yields reasonable perl string';
    is $repr.perl, 'ADTRepr.new(Foo, FooCtor1of3 => 0, FooCtor2of3 => 1, FooCtor3of3 => 2)', 
        '.repr.perl';

    my ($ctor1, $ctor2, $ctor3) = $repr.ctors;

    is $ctor1.name, 'FooCtor1of3', '1st ctor name';
    is $ctor2.name, 'FooCtor2of3', '2nd ctor name';
    is $ctor3.name, 'FooCtor3of3', '3rd ctor name';

    is $ctor1.arity, 0, '1st ctor arity';
    is $ctor2.arity, 1, '2nd ctor arity';
    is $ctor3.arity, 2, '3rd ctor arity';

    cmp_ok $ctor1.ADT, '===', $repr, '1st ctor .ADT';
    cmp_ok $ctor2.ADT, '===', $repr, '2nd ctor .ADT';
    cmp_ok $ctor3.ADT, '===', $repr, '3rd ctor .ADT';
}

# makeMatcher -----------------------------------------------------------------

#my Foo:D $x = $VarT('x');
#my Foo:D $y = $VarT('y');


{ # makeMatcher parameter checking
    dies_ok { makeMatcher }, 'throws with no args';
    throws_like { makeMatcher(Int) }, X::TypeCheck::Binding, 'throws with 1st arg a type that isnt a subtype of ADT';
    throws_like { makeMatcher(5) }, X::TypeCheck::Binding, 'throws with 1st arg an instance of a non-ADT subtype';
    
    throws_like { makeMatcher($fooInstance) }, X::AdHoc, 'throws with 1st arg an *instance* of an ADT subtype';
}

{ # output of makeMatcher (a concrete matcher)
    my (&fooMatcher, &barMatcher);

    lives_ok { &barMatcher = makeMatcher(Bar) }, 'makeMatcher output does Callable (for ADT Bar)'
        or die;
    is &barMatcher.WHICH, 'BarMatcher', '&barMatcher.WHICH';

    lives_ok { &fooMatcher = makeMatcher(Foo) }, 'makeMatcher output does Callable (for ADT Foo)'
        or die;
    is &fooMatcher.WHICH, 'FooMatcher', '&fooMatcher.WHICH';

    is &barMatcher.WHICH, 'BarMatcher', '&barMatcher.WHICH';

    isnt &fooMatcher.WHERE, &barMatcher.WHERE, '&fooMatcher and &barMatcher should NOT be the same';
    
    
    { # concrete matcher .perl (the source of itself)
        my $src = &fooMatcher.perl;
        diag $src;
        my $evalResult;
        lives_ok { $evalResult = EVAL($src) }, 'matcher\'s .perl returns valid Perl6';
        is $evalResult.HOW.Str.substr(0, 26), 'Perl6::Metamodel::ClassHOW', 'EVAL\'ing &fooMatcher.perl gives a class';
        is $evalResult.WHICH, 'FooMatcher', 'EVAL\'ing &fooMatcher.perl gives a class named FooMatcher';
    }

    { # concrete matcher parameter checking
        throws_like { fooMatcher }, X::AdHoc, 'calling matcher with no args throws (bare call `matcher`)';
        throws_like { fooMatcher() }, X::AdHoc, 'calling matcher with no args throws (`matcher()`)';
        throws_like { &fooMatcher() }, X::AdHoc, 'calling matcher with no args throws (`&matcher()`)';

        throws_like { &fooMatcher($barInstance) }, X::AdHoc,
            'calling matcher with instance of another ADT throws (`&fooMatcher($barInstance)`)';

        throws_like { &barMatcher($fooInstance) }, X::AdHoc,
            'calling matcher with instance of another ADT throws (`&barMatcher($fooInstance)`)';

        #throws_like { &fooMatcher($fooInstance) }, X::Typing::ArgBinding,
        #    'calling matcher with instance but without any callbacks as named params throws (`&fooMatcher($fooInstance)`)';
    }

    my $on1st = -> Mu {};
    my $on2nd = -> $a {};
    my $on3rd = -> $a, $b {};
    
    my $result;
    lives_ok {$result = &fooMatcher($fooInstance1o3, FooCtor1o3 => $on1st, FooCtor2o3 => $on2nd, FooCtor2o3 => $on2nd)},
        'lives: calling matcher with instance and callbacks for all ctors (same order as declared)';
    lives_ok {$result = &fooMatcher($fooInstance1o3, FooCtor2o3 => $on2nd, FooCtor2o3 => $on2nd, FooCtor1o3 => $on1st)},
        'lives: calling matcher with instance and callbacks for all ctors (reversed order as declared)';

}
