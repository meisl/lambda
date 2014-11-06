use v6;

use Test;
use Test::Util;
use Lambda::Base;
use Lambda::Boolean;

use Lambda::TermADT;

plan 73;


my $x ::= $VarT('x');
my $y ::= $VarT('y');
my $z ::= $VarT('z');
my $c ::= $ConstT('c');

{ # Term->source
    is_properLambdaFn($Term2source);

    is $Term2source.symbol, 'Term->source', '$Term2source.symbol';
    is $Term2source.Str,    'Term->source', '$Term2source.Str';

    my sub has_source(*@tests) {
        for @tests -> $test {
            my $term       = $test.key;
            my $termStr    = $Term2Str($term);
            my $expected   = $test.value;
            my $desc       = "(Term->source $termStr)";
            
            is($Term2source($term), $expected, $desc);
        }
    }

    has_source(
        $x                                                          => 'x',
        $c                                                          => '"c"',
        $ConstT(5)                                                  => '5',
        $AppT($x, $c)                                               => '(x "c")',
        $AppT($x, $x)                                               => '(x x)',
        $AppT($x, $y)                                               => '(x y)',
        $LamT($x, $c)                                               => '(λx."c")',
        $LamT($x, $x)                                               => '(λx.x)',
        $LamT($x, $AppT($x, $x))                                    => '(λx.(x x))',
        $LamT($x, $AppT($x, $c))                                    => '(λx.(x "c"))',
        $LamT($x, $AppT($x, $y))                                    => '(λx.(x y))',
        $LamT($x, $AppT($y, $x))                                    => '(λx.(y x))',
        $LamT($x, $AppT($x, $LamT($y, $AppT($x, $y))))              => '(λx.(x (λy.(x y))))',
        $AppT($LamT($y, $AppT($x, $y)), $y)                         => '((λy.(x y)) y)',
        $AppT($LamT($x, $AppT($y, $x)), $LamT($y, $AppT($x, $y)))   => '((λx.(y x)) (λy.(x y)))',
        $LamT($x, $AppT($LamT($y, $AppT($z, $y)), $x))              => '(λx.((λy.(z y)) x))',
        $LamT($x, $AppT($LamT($y, $AppT($x, $y)), $x))              => '(λx.((λy.(x y)) x))',
        $LamT($x, $AppT($LamT($x, $AppT($x, $y)), $x))              => '(λx.((λx.(x y)) x))',
    );
}


{ # Term->children
    is_properLambdaFn($Term2children);

    is $Term2children.symbol, 'Term->children', '$Term2children.symbol';
    is $Term2children.Str,    'Term->children', '$Term2children.Str';

    my $x = $VarT('x');
    my $y = $VarT('y');
    my $c = $ConstT('c');

    $has_length($Term2children($x), 0, "(Term->children $x)");
    $has_length($Term2children($c), 0, "(Term->children $c)");

    my $cs;
    
    my $t1 = $AppT($x, $y);
    $cs = $Term2children($t1);
    $has_length($cs, 2, "(Term->children $t1)");
    $contains_ok($x, $cs, "(Term->children $t1)");
    $contains_ok($y, $cs, "(Term->children $t1)");
    
    my $t2 = $AppT($t1, $c);
    $cs = $Term2children($t2);
    $has_length($cs, 2, "(Term->children $t2)");
    $contains_ok($t1, $cs, "(Term->children $t2)");
    $contains_ok($c,  $cs, "(Term->children $t2)");
    
    my $t3 = $LamT($x, $t2);
    $cs = $Term2children($t3);
    $has_length($cs, 2, "(Term->children $t3)");
    $contains_ok($x,  $cs, "(Term->children $t3)");
    $contains_ok($t2, $cs, "(Term->children $t3)");
}


{ # predicate selfApp?
    is_properLambdaFn($is-selfApp);

    is $is-selfApp.symbol, 'selfApp?', '$is-selfApp.symbol';
    is $is-selfApp.Str,    'selfApp?', '$is-selfApp.Str';

    my sub is_selfApp(*@tests) {
        for @tests -> $test {
            my $term       = $test.key;
            my $termSrc    = $Term2source($term);
            my $expected   = $test.value;
            my $desc       = "(selfApp? '$termSrc) -> $expected";
            
            is($is-selfApp($term), $expected, $desc);
        }
    }

    is_selfApp(
        $x                                                          => $false,  # x
        $c                                                          => $false,  # "c"
        $ConstT(5)                                                  => $false,  # 5
        $AppT($x, $c)                                               => $false,  # (x "c")
        $AppT($x, $x)                                               => $true,   # (x x)
        $AppT($y, $y)                                               => $true,   # (y y)
        $AppT($x, $y)                                               => $false,  # (x y)
        $LamT($x, $c)                                               => $false,  # λx."c"
        $LamT($x, $x)                                               => $false,  # λx.x
        $LamT($x, $AppT($x, $x))                                    => $false,  # λx.x x    # omega
        $LamT($y, $AppT($y, $y))                                    => $false,  # λy.y y    # omega
        $LamT($x, $AppT($x, $c))                                    => $false,  # λx.x "c"
        $LamT($x, $AppT($x, $y))                                    => $false,  # λx.x y
        $LamT($x, $AppT($y, $x))                                    => $false,  # λx.y x
        $AppT($LamT($x, $AppT($x, $x)), $LamT($x, $AppT($x, $x)))   => $false,  # ((λx.x x) (λx.x x))    # Omega = (omega omega)
        $AppT($LamT($x, $AppT($x, $x)), $LamT($y, $AppT($y, $y)))   => $false,  # ((λx.x x) (λy.y y))    # Omega = (omega omega)
    );
}


{ # predicate omega?
    is_properLambdaFn($is-omega);

    is $is-omega.symbol, 'ω?', '$is-omega.symbol';
    is $is-omega.Str,    'ω?', '$is-omega.Str';

    my sub is_omega(*@tests) {
        for @tests -> $test {
            my $term       = $test.key;
            my $termSrc    = $Term2source($term);
            my $expected   = $test.value;
            my $desc       = "(ω? '$termSrc) -> $expected";
            
            is($is-omega($term), $expected, $desc);
        }
    }

    is_omega(
        $x                                                          => $false,  # x
        $c                                                          => $false,  # "c"
        $ConstT(5)                                                  => $false,  # 5
        $AppT($x, $c)                                               => $false,  # (x "c")
        $AppT($x, $x)                                               => $false,  # (x x)
        $AppT($y, $y)                                               => $false,  # (y y)
        $AppT($x, $y)                                               => $false,  # (x y)
        $LamT($x, $c)                                               => $false,  # λx."c"
        $LamT($x, $x)                                               => $false,  # λx.x
        $LamT($x, $AppT($x, $x))                                    => $true,   # λx.x x    # omega
        $LamT($y, $AppT($y, $y))                                    => $true,   # λy.y y    # omega
        $LamT($x, $AppT($x, $c))                                    => $false,  # λx.x "c"
        $LamT($x, $AppT($x, $y))                                    => $false,  # λx.x y
        $LamT($x, $AppT($y, $x))                                    => $false,  # λx.y x
        $AppT($LamT($x, $AppT($x, $x)), $LamT($x, $AppT($x, $x)))   => $false,  # ((λx.x x) (λx.x x))    # Omega = (omega omega)
        $AppT($LamT($x, $AppT($x, $x)), $LamT($y, $AppT($y, $y)))   => $false,  # ((λx.x x) (λy.y y))    # Omega = (omega omega)
    );
}