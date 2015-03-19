use v6;
use Test;

use Lambda::BaseP6;
use Lambda::Boolean;
use Lambda::TermADT;

use Lambda::LambdaGrammar;


my $time = now;


my $x  ::= $VarT('x');
my $y  ::= $VarT('y');
my $z  ::= $VarT('z');
my $c  ::= $ConstT('c');

my $xx ::= $AppT($x, $x);
my $xy ::= $AppT($x, $y);
my $xz ::= $AppT($x, $z);
my $xc ::= $AppT($x, $c);

my $yx ::= $AppT($y, $x);
my $yy ::= $AppT($y, $y);
my $yz ::= $AppT($y, $z);
my $yc ::= $AppT($y, $c);

my $zx ::= $AppT($z, $x);
my $zy ::= $AppT($z, $y);
my $zz ::= $AppT($z, $z);
my $zc ::= $AppT($z, $c);

my $xyc ::= $AppT($xy, $c);

my $Lx_x  ::= $LamT('x', $x);
my $Lx_xy ::= $LamT('x', $xy);
my $Ly_xy ::= $LamT('y', $xy);

my $omegaX  ::= $LamT('x', $xx);  # (λx.x x)              # omega ("in x")
my $OmegaXX ::= $AppT($omegaX, $omegaX);    # ((λx.x x) (λx.x x))   # Omega = (omega omega)
my $omegaY  ::= $LamT('y', $yy);  # (λy.y y)              # omega ("in y")
my $OmegaYY ::= $AppT($omegaY, $omegaY);    # ((λy.y y) (λy.y y))   # Omega (one flavour of...)
my $OmegaXY ::= $AppT($omegaX, $omegaY);    # ((λy.y y) (λy.y y))   # Omega (one flavour of...)
my $OmegaYX ::= $AppT($omegaY, $omegaX);    # ((λy.y y) (λx.x x))   # Omega (one flavour of...)

our %terms is export = %(
    'x'                        => $x,
    'y'                        => $y,
    'z'                        => $z,
    '"c"'                      => $c,
    '5'                        => $ConstT(5),

    '(x x)'                    => $xx,
    '(x y)'                    => $xy,
    '(x z)'                    => $xz,
    '(x "c")'                  => $xc,

    '(y x)'                    => $yx,
    '(y y)'                    => $yy,
    '(y z)'                    => $yz,
    '(y "c")'                  => $yc,

    '(z x)'                    => $zx,
    '(z y)'                    => $zy,
    '(z z)'                    => $zz,
    '(z "c")'                  => $zc,

    '((x y) "c")'              => $xyc,
    
    '(λx.((x y) "c"))'         => $LamT("x", $xyc),

    '(λx.x)'                   => $Lx_x,
    '(λx.(x y))'               => $Lx_xy,
    '(λy.(x y))'               => $Ly_xy,

    '(λx."c")'                 => $LamT('x', $c),
    '(λx.(x "c"))'             => $LamT('x', $xc),
    '(λx.(x y))'               => $Lx_xy,
    '(λx.(y x))'               => $LamT('x', $yx),
    '(λx.(x (λy.(x y))))'      => $LamT('x', $AppT($x, $Ly_xy)),
    '((λy.(x y)) y)'           => $AppT($Ly_xy, $y),
    '((λx.(y x)) (λy.(x y)))'  => $AppT($LamT('x', $yx), $Ly_xy),
    '(λx.((λy.(z y)) x))'      => $LamT('x', $AppT($LamT('y', $AppT($z, $y)), $x)),
    '(λx.((λy.(x y)) x))'      => $LamT('x', $AppT($Ly_xy, $x)),
    '(λx.((λx.(x y)) x))'      => $LamT('x', $AppT($Lx_xy, $x)),
    '(y y)'                    => $yy,
    '((λx.(x x)) (y y))'       => $AppT($omegaX, $yy),
    '((y y) (λx.(x x)))'       => $AppT($yy, $omegaX),
    '(x (x y))'                => $AppT($x, $xy),
    '(λz.(x (x y)))'           => $LamT('z', $AppT($x, $xy)),

    '(λx.(x x))'               => $omegaX,
    '(λy.(y y))'               => $omegaY,
    '((λx.(x x)) (λx.(x x)))'  => $OmegaXX,
    '((λy.(y y)) (λy.(y y)))'  => $OmegaYY,
    '((λx.(x x)) (λy.(y y)))'  => $OmegaXY,
    '((λy.(y y)) (λx.(x x)))'  => $OmegaYX,
);
%terms{'omegaX'}  = $omegaX;
%terms{'omegaY'}  = $omegaY;
%terms{'OmegaXX'} = $OmegaXX;
%terms{'OmegaXY'} = $OmegaXY;
%terms{'OmegaYX'} = $OmegaYX;
%terms{'omegaYY'} = $OmegaYY;

%terms{'ω'}   = $omegaX;
%terms{'Ω'}   = $OmegaXX;

%terms{'ωX'}  = $omegaX;
%terms{'ωY'}  = $omegaY;
%terms{'ΩXX'} = $OmegaXX;
%terms{'ΩXY'} = $OmegaXY;
%terms{'ΩYX'} = $OmegaYX;
%terms{'ΩYY'} = $OmegaYY;

# for convenience: make stuff available without surrounding parens as well
for %terms.pairs -> (:$key, :$value) {
    if $key.substr(0, 1) eq '(' {
        %terms{$key.substr(1, *-1)} = $value;
    }
}
$time = (now.Real - $time.Real).round(0.2);
diag "$time sec consumed for test-terms initialization";


#`{
    my $maxKeyLen = @(0, %terms.keys).reduce(-> $currentMax, $key { max($currentMax, $key.chars) });
    my $termsSrcP6 = %terms.pairs.map(-> (:$key, :$value) {
        sprintf("%-{$maxKeyLen+3}s => %s", "'$key'", $Term2sourceP6($value));
     }).join(",\n    ");
    $termsSrcP6 = '%(' ~ "\n    " ~ $termsSrcP6 ~ "\n);";
    diag "our \%terms is export = $termsSrcP6";

    diag "termCount: {%terms.elems}";
    diag "maxKeyLen: $maxKeyLen";
}


multi sub prefix:<`>(Str:D $termIdentifier -->TTerm:D) is export {
    my $term = %terms{$termIdentifier};
    if not $term.defined {
        my $msg = "unprepared test term: '$termIdentifier'";
        try {
            $term = parseLambda($termIdentifier);
            $msg ~= " - you may want to add it to %terms in {$?FILE}:\n    '$termIdentifier'         => {$Term2sourceP6($term)},";
        }
        $msg ~= " - $!"
            if $!;
        die $msg;
    }
    return $term;
}

sub testTermFn($f, :$argToStr = *.Str, :$expectedToStr, *@tests) is export {
    my Str $fgist = $f.gist;
    subtest({
        for @tests -> $test {
            my Any   $arg = $test.key;
            
            my TTerm $term;
            my Str   $termSrc;
            if $arg ~~ TTerm {
                $term    = $arg;
                $termSrc = $Term2source($term);
                # we got a new one - add it!
                %terms{$termSrc} = $term;
            } elsif $arg ~~ Str {
                $term    = `$arg;
                $termSrc = $Term2source($term);
            } else {
                die "expected either a TTerm or a Str but got $arg.perl";
            }

            my Str   $termStr       = $argToStr($term);
            my Any   $expected      = $test.value;
            my Str   $expectedStr   = $expectedToStr.defined
                                        ?? ' -> ' ~ $expectedToStr($expected)
                                        !! '';
            my $desc = "($fgist $termStr)$expectedStr";

            is($f($term), $expected, $desc);
        }
    }, "$fgist on various inputs");
}

my sub is_eq-msg(TTerm:D $actual, TTerm:D $expected) {
    "`{$Term2source($actual)}  should equal  `{$Term2source($expected)}"
}

my sub is_eq-diag(TTerm:D $actual, TTerm:D $expected) {
    my $actualSrc = $Term2source($actual);
    my $actualStr = $actual.Str;
    my $expectedSrc = $Term2source($expected);
    my $expectedStr = $expected.Str;
    my $n = max($actualSrc.chars, $expectedSrc.chars);
    diag sprintf("expected: `%-{$n}s   /   `%s\n     got: `%-{$n}s   /   `%s",
        $actualSrc,   $actualStr,
        $expectedSrc, $expectedStr
    );
    False;
}

multi sub is_eq(TTerm:D $actual, TTerm:D $expected, Str $msg?) is export {
    ok($Term-eq($actual, $expected) === $true, $msg // is_eq-msg($actual, $expected) )
        or is_eq-diag($actual, $expected);
}
