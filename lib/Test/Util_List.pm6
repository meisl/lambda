use v6;

use Test;
use Lambda::BaseP6;
use Lambda::Conversion;
use Lambda::ListADT;

module Test::Util_List;


my $tripleEq = -> $a, $b { $a === $b } does role {
    has $.Str = '===';
};

constant $contains_ok is export = lambdaFn(
    'contains_ok', 'λy.λxs.λxsDesc.exists (λe.y === e) xs',
    -> $y, TList:D $xs, Str:D $xsDesc {
        ok(convertTBool2P6Bool($exists(-> $e { convert2Lambda($e === $y) }, $xs)), "(contains_ok $y $xsDesc)")
            or diag("searched: $y\n in list: $xs") and False;
    }
);

constant $has_length is export = lambdaFn(
    'has_length', 'λxs.λn.λxsDesc.(eq? n (length xs))',
    -> TList:D $xs, Int:D $n, Str:D $xsDesc {
        is($length($xs), $n, "(eq? $n (length $xsDesc))")
            or diag(" of list: $xs") and False;
    }
);


my sub fail_is_in(Str $msg, $elem, @list, $cmpStr) {
    diag sprintf("\nexpected (as elem): %s\n     got this list: (%s)\n%18s: %s",
        $elem,
        @list.map(*.Str).join(', '),
        'comparison used', $cmpStr
    );
    ok(False, $msg);
}

my multi sub is_in($elem, @list, Str $msg?, :&cmp = $tripleEq) is export {
    my $m = $msg // "$elem occurs in ({@list.join(', ')})";
    for @list -> $e {
        if &cmp($e, $elem) {
            return ok(True, $m);
        }
        fail_is_in($m, $elem, @list, &cmp);
    }
}

my sub fail_isnt_in(Str $msg, $elem, @list, $idx, $cmpStr) {
    diag sprintf("\nexpected to NOT occur: %s\n     got this list: (%s)\n:         found at idx: %d\n%21s: %s",
        $elem,
        @list.map(*.Str).join(', '),
        $idx,
        'comparison used', $cmpStr
    );
    ok(False, $msg);
}

my multi sub isnt_in($elem, @list, Str $msg?, :&cmp = $tripleEq) is export {
    my $m = $msg // "$elem does NOT occur in ({@list.join(', ')})";
    my $idx = 0;
    for @list -> $e {
        if &cmp($e, $elem) {
            fail_isnt_in($m, $elem, @list, $idx, &cmp);
        }
        $idx++;
    }
    ok(True, $m);
}

my sub fail_eq-List_elem(Str $msg, Int $idx, $actualElem, $expectedElem, $cmpStr) {
    diag sprintf("\nexpected (at index $idx): %s\n     got (at index $idx): %s\n%{20+$idx.Str.chars}s: %s",
        $expectedElem, $actualElem,
        'comparison used', $cmpStr
    );
    ok(False, $msg);
}

my sub fail_eq-List_tooFew(Str $msg, @actual, @expected) {
    die "expected {@actual.perl} to have LESS elems than {@expected.perl}"
        unless @actual.elems < @expected.elems;

    diag sprintf("\nexpected: %d more, namely %s\n     got: NOTHING after %d elements",
        @expected.elems - @actual.elems,
        @expected[@actual.elems .. *-1].join(', '),
        @actual.elems
    );
    ok(False, $msg);
}

my sub fail_eq-List_tooMany(Str $msg, @actual, @expected) {
    die "expected {@actual.perl} to have MORE elems than {@expected.perl}"
        unless @actual.elems > @expected.elems;

    diag sprintf("\nexpected: NOTHING after %d elements\n     got: %d more, nameley %s",
        @expected.elems,
        @actual.elems - @expected.elems,
        @actual[@expected.elems .. *-1].join(', ')
    );
    ok(False, $msg);
}

sub is_eq-List(TList:D $actual, @expected, Str $msg?, :&cmp = $tripleEq) is export {
    my @actual = convertTList2P6Array($actual);
    my $m = $msg // "{$List2Str($actual)} equals {$List2Str(convert2Lambda(@expected))}";

    my $idx = 0;
    for @actual Z @expected -> $a, $x {
        if not &cmp($a, $x) {
            return fail_eq-List_elem($m, $idx, $a, $x, &cmp);
        }
        $idx++;
    }
    if @actual.elems < @expected.elems {
        fail_eq-List_tooFew($m, @actual, @expected);
    } elsif @actual.elems > @expected.elems {
        fail_eq-List_tooMany($m, @actual, @expected);
    } else {
        ok(True, $m);
    }
}

