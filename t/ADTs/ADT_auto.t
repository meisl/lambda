use v6;
use Test;
use Test::Util;

use Lambda::BaseP6;

# module under test:
use Lambda::ADT_auto;

plan 11;


# prep ------------------------------------------------------------------------

# a sample ADT
role Foo does ADT {
}
my $fooInstance = lambdaFn( 'aFoo', 'λNYI."not yet implemented', -> $client { $client }) does Foo;

# another sample ADT
role Bar does ADT {
}
my $barInstance = lambdaFn( 'aBar', 'λNYI."not yet implemented', -> $client { $client }) does Bar;


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
    my &fooMatcher;
    lives_ok { &fooMatcher = makeMatcher(Foo) }, 'makeMatcher output does Callable (for ADT Foo)'
        or die;
    my &barMatcher;
    lives_ok { &barMatcher = makeMatcher(Bar) }, 'makeMatcher output does Callable (for ADT Bar)'
        or die;

    my $src = &fooMatcher.perl;
    diag $src;
    lives_ok { 
        my class GotPerlSrc {}; # ugly: got to have this in scope for successful EVAL
        EVAL($src) 
    }, 'matcher\'s .perl returns valid Perl6';

    { # concrete matcher parameter checking
        throws_like { fooMatcher }, X::AdHoc, 'calling matcher with no args throws (bare call `matcher`)';
        throws_like { fooMatcher() }, X::AdHoc, 'calling matcher with no args throws (`matcher()`)';
        throws_like { &fooMatcher() }, X::AdHoc, 'calling matcher with no args throws (`&matcher()`)';

        throws_like { &fooMatcher($barInstance) }, X::AdHoc,
            'calling matcher with instance of another ADT throws (`&fooMatcher($barInstance)`)';
    }

}
