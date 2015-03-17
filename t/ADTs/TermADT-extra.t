use v6;
use Test;
use Test::Util;
use Test::Util_Lambda;
use Test::Util_List;

use Lambda::BaseP6;
use Lambda::Boolean;


# module under test:
use Lambda::TermADT;

plan 153;


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

my $omegaX  ::= $LamT('x', $xx);  # (λx.x x)              # omega ("in x")
my $OmegaXX ::= $AppT($omegaX, $omegaX);    # ((λx.x x) (λx.x x))   # Omega = (omega omega)
my $omegaY  ::= $LamT('y', $yy);  # (λy.y y)              # omega ("in y")
my $OmegaYY ::= $AppT($omegaY, $omegaY);    # ((λy.y y) (λy.y y))   # Omega (one flavour of...)
my $OmegaXY ::= $AppT($omegaX, $omegaY);    # ((λy.y y) (λy.y y))   # Omega (one flavour of...)
my $OmegaYX ::= $AppT($omegaY, $omegaX);    # ((λy.y y) (λx.x x))   # Omega (one flavour of...)

my $testCount = 0;
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

    '(λx.x)'                   => $LamT('x', $x),

    '(λx."c")'                 => $LamT('x', $c),
    '(λx.(x "c"))'             => $LamT('x', $xc),
    '(λx.(x y))'               => $LamT('x', $xy),
    '(λx.(y x))'               => $LamT('x', $yx),
    '(λx.(x (λy.(x y))))'      => $LamT('x', $AppT($x, $LamT('y', $xy))),
    '((λy.(x y)) y)'           => $AppT($LamT('y', $xy), $y),
    '((λx.(y x)) (λy.(x y)))'  => $AppT($LamT('x', $yx), $LamT('y', $xy)),
    '(λx.((λy.(z y)) x))'      => $LamT('x', $AppT($LamT('y', $AppT($z, $y)), $x)),
    '(λx.((λy.(x y)) x))'      => $LamT('x', $AppT($LamT('y', $xy), $x)),
    '(λx.((λx.(x y)) x))'      => $LamT('x', $AppT($LamT('x', $xy), $x)),
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

my sub test($f, :$argToStr = *.Str, :$expToStr, *@tests) {
    for @tests -> $test {
        my Any   $arg = $test.key;
        my TTerm $term;
        if $arg ~~ TTerm {
            $term = $arg;
        } elsif $arg ~~ Str {
            $term = %terms{$arg} // die "unprepared test term: '$arg'"
        } else {
            die "expected either a TTerm or a Str but got $arg.perl"
        }
        my Str   $termStr       = $argToStr($term);
        my Str   $termSrc       = $Term2source($term);
        my Any   $expected      = $test.value;
        my Str   $expectedStr   = $expToStr.defined
                                    ?? ' -> ' ~ $expToStr($expected)
                                    !! '';
        my $desc = "({$f.gist} $termStr)$expectedStr";
        
        $testCount++;
        #%terms{$termSrc} = $term;

        is($f($term), $expected, $desc);
    }
}


{ # Term->source
    is_properLambdaFn($Term2source, 'Term->source');

    test( $Term2source, :argToStr($Term2Str),
        'x'                         => 'x',
        '"c"'                       => '"c"',
        '5'                         => '5',
        '(x "c")'                   => '(x "c")',
        '(x x)'                     => '(x x)',
        '(x y)'                     => '(x y)',
        '(λx."c")'                  => '(λx."c")',
        '(λx.x)'                    => '(λx.x)',
        '(λx.(x x))'                => '(λx.(x x))',
        '(λx.(x "c"))'              => '(λx.(x "c"))',
        '(λx.(x y))'                => '(λx.(x y))',
        '(λx.(y x))'                => '(λx.(y x))',
        '(λx.(x (λy.(x y))))'       => '(λx.(x (λy.(x y))))',
        '((λy.(x y)) y)'            => '((λy.(x y)) y)',
        '((λx.(y x)) (λy.(x y)))'   => '((λx.(y x)) (λy.(x y)))',
        '(λx.((λy.(z y)) x))'       => '(λx.((λy.(z y)) x))',
        '(λx.((λy.(x y)) x))'       => '(λx.((λy.(x y)) x))',
        '(λx.((λx.(x y)) x))'       => '(λx.((λx.(x y)) x))',
    );
}


{ # Term->children
    is_properLambdaFn($Term2children, 'Term->children');

    $has_length($Term2children($x), 0, "(Term->children $x)");
    $has_length($Term2children($c), 0, "(Term->children $c)");

    my $cs;

    $cs = $Term2children($x);   # x
    $has_length($cs, 0, "(Term->children $x) / a VarT has no children");

    $cs = $Term2children($c);   # "c"
    $has_length($cs, 0, "(Term->children $c) / a ConstT has no children");
    
    my $t1 = $xy;     # (x y)
    $cs = $Term2children($t1);
    $has_length($cs, 2, "(Term->children $t1) / an AppT has two children (func and arg)");
    $contains_ok($x, $cs, "(Term->children $t1)");
    $contains_ok($y, $cs, "(Term->children $t1)");
    
    my $t2 = $AppT($t1, $c);    # ((x y) "c")
    $cs = $Term2children($t2);
    $has_length($cs, 2, "(Term->children $t2) / an AppT has two children (func and arg)");
    $contains_ok($t1, $cs, "(Term->children $t2)") or die;
    $contains_ok($c,  $cs, "(Term->children $t2)");
    
    my $t3 = $LamT('x', $t2);    # (λx.((x y) "c"))
    $cs = $Term2children($t3);
    $has_length($cs, 1, "(Term->children $t3) / a LamT has one child (its body)");
    $contains_ok($t2, $cs, "(Term->children $t3)");
}


{ # predicate selfApp?
    is_properLambdaFn($is-selfApp, 'selfApp?');

    test( $is-selfApp, :argToStr($Term2source), :expToStr(-> $x {$x.Str}),
        'x'             => $false,
        '"c"'           => $false,
        '5'             => $false,
        '(x "c")'       => $false,
        '(x x)'         => $true, 
        '(y y)'         => $true, 
        '(x y)'         => $false,
        'λx."c"'        => $false,
        'λx.x'          => $false,
        'ωX'            => $false,  # 'λx.(x x)
        'ωY'            => $false,  # 'λy.(y y)
        'λx.(x "c")'    => $false,
        'λx.(x y)'      => $false,
        'λx.(y x)'      => $false,
        'ΩXX'           => $false,  # (ωX ωX)
        'ΩYY'           => $false,  # (ωY ωY)
    );
}

{ # predicate selfAppOfVar?
    is_properLambdaFn($is-selfAppOfVar, 'selfAppOfVar?');
    my $f;

    $f = $is-selfAppOfVar($x) but Definition("{$is-selfAppOfVar.name} $x");
    test($f, :argToStr($Term2source), :expToStr(-> $x {$x.Str}),
        'x'             => $false,
        '"c"'           => $false,
        '5'             => $false,
        '(x "c")'       => $false,
        '(x x)'         => $true, 
        '(y y)'         => $false,  # [wrong var]
        '(x y)'         => $false,
        'λx."c"'        => $false,
        'λx.x'          => $false,
        'ωX'            => $false,  # 'λx.(x x)
        'ωY'            => $false,  # 'λy.(y y)
        'λx.(x "c")'    => $false,
        'λx.(x y)'      => $false,
        'λx.(y x)'      => $false,
        'ΩXX'           => $false,  # (ωX ωX)
        'ΩYY'           => $false,  # (ωY ωY)
    );

    $f = $is-selfAppOfVar($y) but Definition("{$is-selfAppOfVar.name} $y");
    test($f, :argToStr($Term2source), :expToStr(-> $x {$x.Str}),
        'x'             => $false,
        '"c"'           => $false,
        '5'             => $false,
        '(x "c")'       => $false,
        '(x x)'         => $false,  #   [wrong var]
        '(y y)'         => $true, 
        '(x y)'         => $false,
        'λx."c"'        => $false,
        'λx.x'          => $false,
        'ωX'            => $false,  # 'λx.(x x)
        'ωY'            => $false,  # 'λy.(y y)
        'λx.(x "c")'    => $false,
        'λx.(x y)'      => $false,
        'λx.(y x)'      => $false,
        'ΩXX'           => $false,  # (ωX ωX)
        'ΩYY'           => $false,  # (ωY ωY)
    );

    $f = $is-selfAppOfVar($c) but Definition("{$is-selfAppOfVar.name} $c");
    test($f, :argToStr($Term2source), :expToStr(-> $x {$x.Str}),
        'x'             => $false,
        '"c"'           => $false,
        '5'             => $false,
        '(x "c")'       => $false,
        '(x x)'         => $false,  #   [passed a ConstT as 1st arg]
        '(y y)'         => $false,  #   [passed a ConstT as 1st arg]
        '(x y)'         => $false,
        'λx."c"'        => $false,
        'λx.x'          => $false,
        'ωX'            => $false,  # 'λx.(x x)
        'ωY'            => $false,  # 'λy.(y y)
        'λx.(x "c")'    => $false,
        'λx.(x y)'      => $false,
        'λx.(y x)'      => $false,
        'ΩXX'           => $false,  # (ωX ωX)
        'ΩYY'           => $false,  # (ωY ωY)
    );
}


{ # predicate omega?
    is_properLambdaFn($is-omega, 'ω?');

    test( $is-omega, :argToStr($Term2source), :expToStr(-> $x {$x.Str}),
        'x'             => $false,
        '"c"'           => $false,
        '5'             => $false,
        '(x "c")'       => $false,
        '(x x)'         => $false,
        '(y y)'         => $false,
        '(x y)'         => $false,
        'λx."c"'        => $false,
        'λx.x'          => $false,
        'ωX'            => $true,   # 'λx.(x x)
        'ωY'            => $true,   # 'λy.(y y)
        'λx.(x "c")'    => $false,
        'λx.(x y)'      => $false,
        'λx.(y x)'      => $false,
        'ΩXX'           => $false,  # (ωX ωX)
        'ΩYY'           => $false,  # (ωY ωY)
    );
}


{ # predicate Ω? ($is-Omega)
    is_properLambdaFn($is-Omega, 'Ω?');

    test( $is-Omega, :argToStr($Term2source), :expToStr(-> $x {$x.Str}),
        'x'                 => $false,
        '"c"'               => $false,
        '5'                 => $false,
        '(x "c")'           => $false,
        '(x x)'             => $false,
        '(y y)'             => $false,
        '(x y)'             => $false,
        'λx."c"'            => $false,
        'λx.x'              => $false,
        'ωX'                => $false,  # 'λx.(x x)
        'ωY'                => $false,  # 'λy.(y y)
        'λx.(x "c")'        => $false,
        'λx.(x y)'          => $false,
        'λx.(y x)'          => $false,
        'ΩXX'               => $true ,  # (ωX ωX)
        'ΩXY'               => $true ,  # (ωX ωY)
        'ΩYX'               => $true ,  # (ωY ωX)
        'ΩYY'               => $true,   # (ωY ωY)
        '(λx.(x x)) (y y)'  => $false,
        '(y y) (λx.(x x))'  => $false,
    );

}

{ # Term->size
    is_properLambdaFn($Term2size, 'Term->size');

    # size of a LamT is 1 + size of body
    # size of an AppT is 1 + size of func + size of arg
    # size of both, a VarT and ConstT is 1

    test( $Term2size, :argToStr($Term2source), :expToStr(-> $x {$x.Str}),
        'x'                         =>  1,
        '"c"'                       =>  1,
        '5'                         =>  1,
        '(x "c")'                   =>  3,
        '(x (x y))'                 =>  5,
        'λz.(x (x y))'              =>  6,
        '(λx.(x (λy.(x y))))'       =>  7,
        '((λy.(x y)) y)'            =>  6,
        '((λx.(y x)) (λy.(x y)))'   =>  9,
        '(λx.((λy.(z y)) x))'       =>  7,
        'ωX'                        =>  4,  # 'λx.(x x)
        'ωY'                        =>  4,  # 'λy.(y y)
        'ΩXX'                       =>  9,  # (ωX ωX)
        'ΩXY'                       =>  9,  # (ωX ωY)
        'ΩYX'                       =>  9,  # (ωY ωX)
        'ΩYY'                       =>  9,  # (ωY ωY)
    );

}

#`{
    my $maxKeyLen = @(0, %terms.keys).reduce(-> $currentMax, $key { max($currentMax, $key.chars) });
    my $termsSrcP6 = %terms.pairs.map(-> (:$key, :$value) {
        sprintf("%-{$maxKeyLen+3}s => %s", "'$key'", $Term2sourceP6($value));
     }).join(",\n    ");
    $termsSrcP6 = '%(' ~ "\n    " ~ $termsSrcP6 ~ "\n);";
    diag "our \%terms is export = $termsSrcP6";

    diag "testCount: $testCount";
    diag "termCount: {%terms.elems}";
    diag "maxKeyLen: $maxKeyLen";
}


