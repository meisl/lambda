use v6;

use Test;
use Test::Util;
use Lambda::Base;
use Lambda::Boolean;

use Lambda::TermADT;

plan 21;


{ # Term->source
    is_properLambdaFn($Term2source);

    is $Term2source.symbol, 'Term->source', '$Term2source.symbol';
    is $Term2source.Str,    'Term->source', '$Term2source.Str';

    my sub test(*@tests) {
        for @tests -> $test {
            my $term       = $test.key;
            my $termStr    = $Term2Str($term);
            my $expected   = $test.value;
            my $desc       = "(Term->source $termStr)";
            
            is($Term2source($term), $expected, $desc);
        }
    }

    my $x = $VarT('x');
    my $y = $VarT('y');
    my $z = $VarT('z');
    my $c = $ConstT('c');
    my $t;

    test(
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
