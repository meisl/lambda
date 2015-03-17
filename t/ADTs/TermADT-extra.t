use v6;
use Test;
use Test::Util;
use Test::Util_Lambda;
use Test::Util_List;

use Lambda::BaseP6;
use Lambda::Boolean;


# module under test:
use Lambda::TermADT;

plan 146;


my $x ::= $VarT('x');
my $y ::= $VarT('y');
my $z ::= $VarT('z');
my $c ::= $ConstT('c');
my $omegaX  ::= $LamT('x', $AppT($x, $x));  # (λx.x x)              # omega ("in x")
my $OmegaXX ::= $AppT($omegaX, $omegaX);    # ((λx.x x) (λx.x x))   # Omega = (omega omega)
my $omegaY  ::= $LamT('y', $AppT($y, $y));  # (λy.y y)              # omega ("in y")
my $OmegaYY ::= $AppT($omegaY, $omegaY);    # ((λy.y y) (λy.y y))   # Omega (one flavour of...)
my $OmegaXY ::= $AppT($omegaX, $omegaY);    # ((λy.y y) (λy.y y))   # Omega (one flavour of...)
my $OmegaYX ::= $AppT($omegaY, $omegaX);    # ((λy.y y) (λx.x x))   # Omega (one flavour of...)

my $testCount = 0;
our %terms is export = %(
    'x'                        => $VarT("x"),
    '"c"'                      => $ConstT("c"),
    '5'                        => $ConstT(5),
    '(x "c")'                  => $AppT($VarT("x"), $ConstT("c")),
    '(x x)'                    => $AppT($VarT("x"), $VarT("x")),
    '(x y)'                    => $AppT($VarT("x"), $VarT("y")),
    '(λx."c")'                 => $LamT("x", $ConstT("c")),
    '(λx.x)'                   => $LamT("x", $VarT("x")),
    '(λx.(x "c"))'             => $LamT("x", $AppT($VarT("x"), $ConstT("c"))),
    '(λx.(x y))'               => $LamT("x", $AppT($VarT("x"), $VarT("y"))),
    '(λx.(y x))'               => $LamT("x", $AppT($VarT("y"), $VarT("x"))),
    '(λx.(x (λy.(x y))))'      => $LamT("x", $AppT($VarT("x"), $LamT("y", $AppT($VarT("x"), $VarT("y"))))),
    '((λy.(x y)) y)'           => $AppT($LamT("y", $AppT($VarT("x"), $VarT("y"))), $VarT("y")),
    '((λx.(y x)) (λy.(x y)))'  => $AppT($LamT("x", $AppT($VarT("y"), $VarT("x"))), $LamT("y", $AppT($VarT("x"), $VarT("y")))),
    '(λx.((λy.(z y)) x))'      => $LamT("x", $AppT($LamT("y", $AppT($VarT("z"), $VarT("y"))), $VarT("x"))),
    '(λx.((λy.(x y)) x))'      => $LamT("x", $AppT($LamT("y", $AppT($VarT("x"), $VarT("y"))), $VarT("x"))),
    '(λx.((λx.(x y)) x))'      => $LamT("x", $AppT($LamT("x", $AppT($VarT("x"), $VarT("y"))), $VarT("x"))),
    '(y y)'                    => $AppT($VarT("y"), $VarT("y")),
    '((λx.(x x)) (y y))'       => $AppT($omegaX, $AppT($VarT("y"), $VarT("y"))),
    '((y y) (λx.(x x)))'       => $AppT($AppT($VarT("y"), $VarT("y")), $omegaX),
    '(x (x y))'                => $AppT($VarT("x"), $AppT($VarT("x"), $VarT("y"))),
    '(λz.(x (x y)))'           => $LamT("z", $AppT($VarT("x"), $AppT($VarT("x"), $VarT("y")))),

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
        my TTerm $term          = $test.key;
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
# 60 60 84

{ # Term->source
    is_properLambdaFn($Term2source, 'Term->source');

    test( $Term2source, :argToStr($Term2Str),
        $x                                                          => 'x',
        $c                                                          => '"c"',
        $ConstT(5)                                                  => '5',
        $AppT($x, $c)                                               => '(x "c")',
        $AppT($x, $x)                                               => '(x x)',
        $AppT($x, $y)                                               => '(x y)',
        $LamT('x', $c)                                              => '(λx."c")',
        $LamT('x', $x)                                              => '(λx.x)',
        $LamT('x', $AppT($x, $x))                                   => '(λx.(x x))',
        $LamT('x', $AppT($x, $c))                                   => '(λx.(x "c"))',
        $LamT('x', $AppT($x, $y))                                   => '(λx.(x y))',
        $LamT('x', $AppT($y, $x))                                   => '(λx.(y x))',
        $LamT('x', $AppT($x, $LamT('y', $AppT($x, $y))))            => '(λx.(x (λy.(x y))))',
        $AppT($LamT('y', $AppT($x, $y)), $y)                        => '((λy.(x y)) y)',
        $AppT($LamT('x', $AppT($y, $x)), $LamT('y', $AppT($x, $y))) => '((λx.(y x)) (λy.(x y)))',
        $LamT('x', $AppT($LamT('y', $AppT($z, $y)), $x))            => '(λx.((λy.(z y)) x))',
        $LamT('x', $AppT($LamT('y', $AppT($x, $y)), $x))            => '(λx.((λy.(x y)) x))',
        $LamT('x', $AppT($LamT('x', $AppT($x, $y)), $x))            => '(λx.((λx.(x y)) x))',
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
    
    my $t1 = $AppT($x, $y);     # (x y)
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
        $x                                                          => $false,  # x
        $c                                                          => $false,  # "c"
        $ConstT(5)                                                  => $false,  # 5
        $AppT($x, $c)                                               => $false,  # (x "c")
        $AppT($x, $x)                                               => $true,   # (x x)
        $AppT($y, $y)                                               => $true,   # (y y)
        $AppT($x, $y)                                               => $false,  # (x y)
        $LamT('x', $c)                                              => $false,  # λx."c"
        $LamT('x', $x)                                              => $false,  # λx.x
        $LamT('x', $AppT($x, $x))                                   => $false,  # λx.x x    # omega
        $LamT('y', $AppT($y, $y))                                   => $false,  # λy.y y    # omega
        $LamT('x', $AppT($x, $c))                                   => $false,  # λx.x "c"
        $LamT('x', $AppT($x, $y))                                   => $false,  # λx.x y
        $LamT('x', $AppT($y, $x))                                   => $false,  # λx.y x
        $AppT($LamT('x', $AppT($x, $x)), $LamT('x', $AppT($x, $x))) => $false,  # ((λx.x x) (λx.x x))    # Omega = (omega omega)
        $AppT($LamT('x', $AppT($x, $x)), $LamT('y', $AppT($y, $y))) => $false,  # ((λx.x x) (λy.y y))    # Omega = (omega omega)
    );
}

{ # predicate selfAppOfVar?
    is_properLambdaFn($is-selfAppOfVar, 'selfAppOfVar?');
    my $f;

    $f = $is-selfAppOfVar($x) but Definition("{$is-selfAppOfVar.name} $x");
    test($f, :argToStr($Term2source), :expToStr(-> $x {$x.Str}),
        $x                                                          => $false,  # x
        $c                                                          => $false,  # "c"
        $ConstT(5)                                                  => $false,  # 5
        $AppT($x, $c)                                               => $false,  # (x "c")
        $AppT($x, $x)                                               => $true,   # (x x)
        $AppT($y, $y)                                               => $false,  # (y y)  [wrong var]
        $AppT($x, $y)                                               => $false,  # (x y)
        $LamT('x', $c)                                              => $false,  # λx."c"
        $LamT('x', $x)                                              => $false,  # λx.x
        $LamT('x', $AppT($x, $x))                                   => $false,  # λx.x x    # omega
        $LamT('y', $AppT($y, $y))                                   => $false,  # λy.y y    # omega
        $LamT('x', $AppT($x, $c))                                   => $false,  # λx.x "c"
        $LamT('x', $AppT($x, $y))                                   => $false,  # λx.x y
        $LamT('x', $AppT($y, $x))                                   => $false,  # λx.y x
        $AppT($LamT('x', $AppT($x, $x)), $LamT('x', $AppT($x, $x))) => $false,  # ((λx.x x) (λx.x x))    # Omega = (omega omega)
        $AppT($LamT('x', $AppT($x, $x)), $LamT('y', $AppT($y, $y))) => $false,  # ((λx.x x) (λy.y y))    # Omega = (omega omega)
    );

    $f = $is-selfAppOfVar($y) but Definition("{$is-selfAppOfVar.name} $y");
    test($f, :argToStr($Term2source), :expToStr(-> $x {$x.Str}),
        $x                                                          => $false,  # x
        $c                                                          => $false,  # "c"
        $ConstT(5)                                                  => $false,  # 5
        $AppT($x, $c)                                               => $false,  # (x "c")
        $AppT($x, $x)                                               => $false,  # (x x)  [wrong var]
        $AppT($y, $y)                                               => $true,   # (y y)
        $AppT($x, $y)                                               => $false,  # (x y)
        $LamT('x', $c)                                              => $false,  # λx."c"
        $LamT('x', $x)                                              => $false,  # λx.x
        $LamT('x', $AppT($x, $x))                                   => $false,  # λx.x x    # omega
        $LamT('y', $AppT($y, $y))                                   => $false,  # λy.y y    # omega
        $LamT('x', $AppT($x, $c))                                   => $false,  # λx.x "c"
        $LamT('x', $AppT($x, $y))                                   => $false,  # λx.x y
        $LamT('x', $AppT($y, $x))                                   => $false,  # λx.y x
        $AppT($LamT('x', $AppT($x, $x)), $LamT('x', $AppT($x, $x))) => $false,  # ((λx.x x) (λx.x x))    # Omega = (omega omega)
        $AppT($LamT('x', $AppT($x, $x)), $LamT('y', $AppT($y, $y))) => $false,  # ((λx.x x) (λy.y y))    # Omega = (omega omega)
    );

    $f = $is-selfAppOfVar($c) but Definition("{$is-selfAppOfVar.name} $c");
    test($f, :argToStr($Term2source), :expToStr(-> $x {$x.Str}),
        $x                                                          => $false,  # x
        $c                                                          => $false,  # "c"
        $ConstT(5)                                                  => $false,  # 5
        $AppT($x, $c)                                               => $false,  # (x "c")
        $AppT($x, $x)                                               => $false,  # (x x)  [passed a ConstT as 1st arg]
        $AppT($y, $y)                                               => $false,  # (y y)  [passed a ConstT as 1st arg]
        $AppT($x, $y)                                               => $false,  # (x y)
        $LamT('x', $c)                                              => $false,  # λx."c"
        $LamT('x', $x)                                              => $false,  # λx.x
        $LamT('x', $AppT($x, $x))                                   => $false,  # λx.x x    # omega
        $LamT('y', $AppT($y, $y))                                   => $false,  # λy.y y    # omega
        $LamT('x', $AppT($x, $c))                                   => $false,  # λx.x "c"
        $LamT('x', $AppT($x, $y))                                   => $false,  # λx.x y
        $LamT('x', $AppT($y, $x))                                   => $false,  # λx.y x
        $AppT($LamT('x', $AppT($x, $x)), $LamT('x', $AppT($x, $x))) => $false,  # ((λx.x x) (λx.x x))    # Omega = (omega omega)
        $AppT($LamT('x', $AppT($x, $x)), $LamT('y', $AppT($y, $y))) => $false,  # ((λx.x x) (λy.y y))    # Omega = (omega omega)
    );

}


{ # predicate omega?
    is_properLambdaFn($is-omega, 'ω?');

    test( $is-omega, :argToStr($Term2source), :expToStr(-> $x {$x.Str}),
        $x                                                          => $false,  # x
        $c                                                          => $false,  # "c"
        $ConstT(5)                                                  => $false,  # 5
        $AppT($x, $c)                                               => $false,  # (x "c")
        $AppT($x, $x)                                               => $false,  # (x x)
        $AppT($y, $y)                                               => $false,  # (y y)
        $AppT($x, $y)                                               => $false,  # (x y)
        $LamT('x', $c)                                              => $false,  # λx."c"
        $LamT('x', $x)                                              => $false,  # λx.x
        $LamT('x', $AppT($x, $x))                                   => $true,   # λx.x x    # omega
        $LamT('y', $AppT($y, $y))                                   => $true,   # λy.y y    # omega
        $LamT('x', $AppT($x, $c))                                   => $false,  # λx.x "c"
        $LamT('x', $AppT($x, $y))                                   => $false,  # λx.x y
        $LamT('x', $AppT($y, $x))                                   => $false,  # λx.y x
        $AppT($LamT('x', $AppT($x, $x)), $LamT('x', $AppT($x, $x))) => $false,  # ((λx.x x) (λx.x x))    # Omega = (omega omega)
        $AppT($LamT('x', $AppT($x, $x)), $LamT('y', $AppT($y, $y))) => $false,  # ((λx.x x) (λy.y y))    # Omega = (omega omega)
    );
}


{ # predicate Omega?
    is_properLambdaFn($is-Omega, 'Ω?');

    test( $is-Omega, :argToStr($Term2source), :expToStr(-> $x {$x.Str}),
        $x                                                          => $false,  # x
        $c                                                          => $false,  # "c"
        $ConstT(5)                                                  => $false,  # 5
        $AppT($x, $c)                                               => $false,  # (x "c")
        $AppT($x, $x)                                               => $false,  # (x x)
        $AppT($y, $y)                                               => $false,  # (y y)
        $AppT($x, $y)                                               => $false,  # (x y)
        $LamT('x', $c)                                              => $false,  # λx."c"
        $LamT('x', $x)                                              => $false,  # λx.x
        $LamT('x', $AppT($x, $x))                                   => $false,  # λx.x x    # omega
        $LamT('y', $AppT($y, $y))                                   => $false,  # λy.y y    # omega
        $LamT('x', $AppT($x, $c))                                   => $false,  # λx.x "c"
        $LamT('x', $AppT($x, $y))                                   => $false,  # λx.x y
        $LamT('x', $AppT($y, $x))                                   => $false,  # λx.y x
        $AppT($LamT('x', $AppT($x, $x)), $LamT('x', $AppT($x, $x))) => $true,   # ((λx.x x) (λx.x x))    # Omega = (omega omega)
        $AppT($LamT('x', $AppT($x, $x)), $LamT('y', $AppT($y, $y))) => $true,   # ((λx.x x) (λy.y y))    # Omega = (omega omega)
        $AppT($LamT('x', $AppT($x, $x)), $AppT($y, $y))             => $false,  # ((λx.x x) (y y))
        $AppT($AppT($y, $y), $LamT('x', $AppT($x, $x)))             => $false,  # ((y y) (λx.x x))
    );

}

{ # Term->size
    is_properLambdaFn($Term2size, 'Term->size');

    # size of a LamT is 1 + size of body
    # size of an AppT is 1 + size of func + size of arg
    # size of both, a VarT and ConstT is 1

    test( $Term2size, :argToStr($Term2source), :expToStr(-> $x {$x.Str}),
        $x                                                          =>  1,  # x
        $c                                                          =>  1,  # "c"
        $ConstT(5)                                                  =>  1,  # 5
        $AppT($x, $c)                                               =>  3,  # (x "c")
        $AppT($x, $AppT($x, $y))                                    =>  5,  # (x (x y))
        $LamT('z', $AppT($x, $AppT($x, $y)))                        =>  6,  # λz.(x (x y))
        $LamT('x', $AppT($x, $LamT('y', $AppT($x, $y))))            =>  7,  # (λx.(x (λy.(x y)))),
        $AppT($LamT('y', $AppT($x, $y)), $y)                        =>  6,  # ((λy.(x y)) y),
        $AppT($LamT('x', $AppT($y, $x)), $LamT('y', $AppT($x, $y))) =>  9,  # ((λx.(y x)) (λy.(x y))),
        $LamT('x', $AppT($LamT('y', $AppT($z, $y)), $x))            =>  7,  # (λx.((λy.(z y)) x)),
        $AppT($LamT('x', $AppT($x, $x)), $LamT('x', $AppT($x, $x))) =>  9,  # ((λx.x x) (λx.x x))    # Omega = (omega omega)
    );

}


my $maxKeyLen = @(0, %terms.keys).reduce(-> $currentMax, $key { max($currentMax, $key.chars) });
my $termsSrcP6 = %terms.pairs.map(-> (:$key, :$value) {
    sprintf("%-{$maxKeyLen+3}s => %s", "'$key'", $Term2sourceP6($value));
 }).join(",\n    ");
$termsSrcP6 = '%(' ~ "\n    " ~ $termsSrcP6 ~ "\n);";
diag "our \%terms is export = $termsSrcP6";
diag "testCount: $testCount";
diag "termCount: {%terms.elems}";
diag "maxKeyLen: $maxKeyLen";




# our %terms is export = %(
#     'x'                        => $VarT("x"),
#     '"c"'                      => $ConstT("c"),
#     '5'                        => $ConstT(5),
#     '(x "c")'                  => $AppT($VarT("x"), $ConstT("c")),
#     '(x x)'                    => $AppT($VarT("x"), $VarT("x")),
#     '(x y)'                    => $AppT($VarT("x"), $VarT("y")),
#     '(λx."c")'                 => $LamT("x", $ConstT("c")),
#     '(λx.x)'                   => $LamT("x", $VarT("x")),
#     '(λx.(x "c"))'             => $LamT("x", $AppT($VarT("x"), $ConstT("c"))),
#     '(λx.(x y))'               => $LamT("x", $AppT($VarT("x"), $VarT("y"))),
#     '(λx.(y x))'               => $LamT("x", $AppT($VarT("y"), $VarT("x"))),
#     '(λx.(x (λy.(x y))))'      => $LamT("x", $AppT($VarT("x"), $LamT("y", $AppT($VarT("x"), $VarT("y"))))),
#     '((λy.(x y)) y)'           => $AppT($LamT("y", $AppT($VarT("x"), $VarT("y"))), $VarT("y")),
#     '((λx.(y x)) (λy.(x y)))'  => $AppT($LamT("x", $AppT($VarT("y"), $VarT("x"))), $LamT("y", $AppT($VarT("x"), $VarT("y")))),
#     '(λx.((λy.(z y)) x))'      => $LamT("x", $AppT($LamT("y", $AppT($VarT("z"), $VarT("y"))), $VarT("x"))),
#     '(λx.((λy.(x y)) x))'      => $LamT("x", $AppT($LamT("y", $AppT($VarT("x"), $VarT("y"))), $VarT("x"))),
#     '(λx.((λx.(x y)) x))'      => $LamT("x", $AppT($LamT("x", $AppT($VarT("x"), $VarT("y"))), $VarT("x"))),
#     '(y y)'                    => $AppT($VarT("y"), $VarT("y")),
#     '((λx.(x x)) (y y))'       => $AppT($LamT("x", $AppT($VarT("x"), $VarT("x"))), $AppT($VarT("y"), $VarT("y"))),
#     '((y y) (λx.(x x)))'       => $AppT($AppT($VarT("y"), $VarT("y")), $LamT("x", $AppT($VarT("x"), $VarT("x")))),
#     '(x (x y))'                => $AppT($VarT("x"), $AppT($VarT("x"), $VarT("y"))),
#     '(λz.(x (x y)))'           => $LamT("z", $AppT($VarT("x"), $AppT($VarT("x"), $VarT("y")))),
#     '(λx.(x x))'               => $LamT("x", $AppT($VarT("x"), $VarT("x"))),
#     '(λy.(y y))'               => $LamT("y", $AppT($VarT("y"), $VarT("y"))),
#     '((λx.(x x)) (λx.(x x)))'  => $AppT($LamT("x", $AppT($VarT("x"), $VarT("x"))), $LamT("x", $AppT($VarT("x"), $VarT("x")))),
#     '((λy.(y y)) (λy.(y y)))'  => $AppT($LamT("y", $AppT($VarT("y"), $VarT("y"))), $LamT("y", $AppT($VarT("y"), $VarT("y")))),
#     '((λx.(x x)) (λy.(y y)))'  => $AppT($LamT("x", $AppT($VarT("x"), $VarT("x"))), $LamT("y", $AppT($VarT("y"), $VarT("y")))),
#     '((λy.(y y)) (λx.(x x)))'  => $AppT($LamT("y", $AppT($VarT("y"), $VarT("y"))), $LamT("x", $AppT($VarT("x"), $VarT("x")))),
#     'omegaX'                   => $LamT("x", $AppT($VarT("x"), $VarT("x"))),
#     'omegaY'                   => $LamT("y", $AppT($VarT("y"), $VarT("y"))),
#     'OmegaXX'                  => $AppT($LamT("x", $AppT($VarT("x"), $VarT("x"))), $LamT("x", $AppT($VarT("x"), $VarT("x")))),
#     'OmegaXY'                  => $AppT($LamT("x", $AppT($VarT("x"), $VarT("x"))), $LamT("y", $AppT($VarT("y"), $VarT("y")))),
#     'OmegaYX'                  => $AppT($LamT("y", $AppT($VarT("y"), $VarT("y"))), $LamT("x", $AppT($VarT("x"), $VarT("x")))),
#     'omegaYY'                  => $AppT($LamT("y", $AppT($VarT("y"), $VarT("y"))), $LamT("y", $AppT($VarT("y"), $VarT("y")))),
#     'ω'                        => $LamT("x", $AppT($VarT("x"), $VarT("x"))),
#     'Ω'                        => $AppT($LamT("x", $AppT($VarT("x"), $VarT("x"))), $LamT("x", $AppT($VarT("x"), $VarT("x")))),
#     'ωX'                       => $LamT("x", $AppT($VarT("x"), $VarT("x"))),
#     'ωY'                       => $LamT("y", $AppT($VarT("y"), $VarT("y"))),
#     'ΩXX'                      => $AppT($LamT("x", $AppT($VarT("x"), $VarT("x"))), $LamT("x", $AppT($VarT("x"), $VarT("x")))),
#     'ΩXY'                      => $AppT($LamT("x", $AppT($VarT("x"), $VarT("x"))), $LamT("y", $AppT($VarT("y"), $VarT("y")))),
#     'ΩYX'                      => $AppT($LamT("y", $AppT($VarT("y"), $VarT("y"))), $LamT("x", $AppT($VarT("x"), $VarT("x")))),
#     'ΩYY'                      => $AppT($LamT("y", $AppT($VarT("y"), $VarT("y"))), $LamT("y", $AppT($VarT("y"), $VarT("y")))),
#     'x "c"'                    => $AppT($VarT("x"), $ConstT("c")),
#     'x x'                      => $AppT($VarT("x"), $VarT("x")),
#     'x y'                      => $AppT($VarT("x"), $VarT("y")),
#     'λx."c"'                   => $LamT("x", $ConstT("c")),
#     'λx.x'                     => $LamT("x", $VarT("x")),
#     'λx.(x "c")'               => $LamT("x", $AppT($VarT("x"), $ConstT("c"))),
#     'λx.(x y)'                 => $LamT("x", $AppT($VarT("x"), $VarT("y"))),
#     'λx.(y x)'                 => $LamT("x", $AppT($VarT("y"), $VarT("x"))),
#     'λx.(x (λy.(x y)))'        => $LamT("x", $AppT($VarT("x"), $LamT("y", $AppT($VarT("x"), $VarT("y"))))),
#     '(λy.(x y)) y'             => $AppT($LamT("y", $AppT($VarT("x"), $VarT("y"))), $VarT("y")),
#     '(λx.(y x)) (λy.(x y))'    => $AppT($LamT("x", $AppT($VarT("y"), $VarT("x"))), $LamT("y", $AppT($VarT("x"), $VarT("y")))),
#     'λx.((λy.(z y)) x)'        => $LamT("x", $AppT($LamT("y", $AppT($VarT("z"), $VarT("y"))), $VarT("x"))),
#     'λx.((λy.(x y)) x)'        => $LamT("x", $AppT($LamT("y", $AppT($VarT("x"), $VarT("y"))), $VarT("x"))),
#     'λx.((λx.(x y)) x)'        => $LamT("x", $AppT($LamT("x", $AppT($VarT("x"), $VarT("y"))), $VarT("x"))),
#     'y y'                      => $AppT($VarT("y"), $VarT("y")),
#     '(λx.(x x)) (y y)'         => $AppT($LamT("x", $AppT($VarT("x"), $VarT("x"))), $AppT($VarT("y"), $VarT("y"))),
#     '(y y) (λx.(x x))'         => $AppT($AppT($VarT("y"), $VarT("y")), $LamT("x", $AppT($VarT("x"), $VarT("x")))),
#     'x (x y)'                  => $AppT($VarT("x"), $AppT($VarT("x"), $VarT("y"))),
#     'λz.(x (x y))'             => $LamT("z", $AppT($VarT("x"), $AppT($VarT("x"), $VarT("y")))),
#     'λx.(x x)'                 => $LamT("x", $AppT($VarT("x"), $VarT("x"))),
#     'λy.(y y)'                 => $LamT("y", $AppT($VarT("y"), $VarT("y"))),
#     '(λx.(x x)) (λx.(x x))'    => $AppT($LamT("x", $AppT($VarT("x"), $VarT("x"))), $LamT("x", $AppT($VarT("x"), $VarT("x")))),
#     '(λy.(y y)) (λy.(y y))'    => $AppT($LamT("y", $AppT($VarT("y"), $VarT("y"))), $LamT("y", $AppT($VarT("y"), $VarT("y")))),
#     '(λx.(x x)) (λy.(y y))'    => $AppT($LamT("x", $AppT($VarT("x"), $VarT("x"))), $LamT("y", $AppT($VarT("y"), $VarT("y")))),
#     '(λy.(y y)) (λx.(x x))'    => $AppT($LamT("y", $AppT($VarT("y"), $VarT("y"))), $LamT("x", $AppT($VarT("x"), $VarT("x"))))
# );
# testCount: 127
# termCount: 67
# maxKeyLen: 23
