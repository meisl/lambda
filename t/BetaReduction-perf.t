use v6;
use Test;

use Lambda::MaybeADT;
use Lambda::TermADT;

use Lambda::P6Currying;

# module under test:
use Lambda::BetaReduction;

plan 5;


my $dc = $VarT('_');    # don't-care variable
my $g = $VarT('g');
my $h = $VarT('h');
my $k = $VarT('k');
my $u = $VarT('u');
my $v = $VarT('v');
my $x = $VarT('x');
my $y = $VarT('y');
my $z = $VarT('z');
my $c = $ConstT('c');

{ # first try with two minimal examples, as a sanity check:
    my ($app, $actual, $actualLambda);

    $app = $AppT($x, $x);
    $actual = $betaReduce($app);
    is $actual, 'None', '(x x) reduces to itself (sanity check)'
        or die;

    $app = $AppT($LamT($x, $x), $x);
    $actual = $Some2value($betaReduce($app));
    $actualLambda = $Term2source($actual);
    is $Term-eq($actual, $x), '#true', "{$Term2source($app)} reduces to x (sanity check)"
        or diag("exp: x\ngot: $actualLambda")
        and die;
}

{ # profiling betaReduce
    my $f1 = $VarT('f1');   # field 1
    my $f2 = $VarT('f2');   # field 2
    my $f3 = $VarT('f3');   # field 3
    my $f4 = $VarT('f4');   # field 4
    my $f5 = $VarT('f5');   # field 5

    my ( $bigTerm, $bigLambda, $expectedTerm, $expectedLambda, $actualTerm, $actualLambda);

    #$make-Ctor-chi_term:
    $bigTerm = $LamT($f1, $LamT($f2, $LamT($f3, $LamT($f4, $LamT($f5, $AppT($LamT($y, $LamT($dc, $y)), $AppT($LamT($g, $LamT($h, $AppT($LamT($y, $LamT($dc, $y)), $AppT($g, $h)))), $AppT($LamT($g, $LamT($h, $AppT($LamT($y, $LamT($dc, $y)), $AppT($g, $h)))), $LamT($k, $AppT($AppT($LamT($k, $AppT($AppT($LamT($k, $AppT($AppT($LamT($k, $AppT($AppT($LamT($k, $AppT($AppT($LamT($x, $x), $k), $f1)), $k), $f2)), $k), $f3)), $k), $f4)), $k), $f5))))))))));
    $bigLambda = '(λf1.(λf2.(λf3.(λf4.(λf5.((λy.(λ_.y)) ((λg.(λh.((λy.(λ_.y)) (g h)))) ((λg.(λh.((λy.(λ_.y)) (g h)))) (λk.(((λk.(((λk.(((λk.(((λk.(((λx.x) k) f1)) k) f2)) k) f3)) k) f4)) k) f5))))))))))';
    is $Term2source($bigTerm), $bigLambda, "\$bigTerm.lambda is $bigLambda";

    $expectedTerm = $LamT($f1, $LamT($f2, $LamT($f3, $LamT($f4, $LamT($f5, $LamT($dc, $LamT($h, $LamT($dc, $LamT($dc, $AppT($AppT($AppT($AppT($AppT($h, $f1), $f2), $f3), $f4), $f5))))))))));
    $expectedLambda = '(λf1.(λf2.(λf3.(λf4.(λf5.(λ_.(λh.(λ_.(λ_.(((((h f1) f2) f3) f4) f5))))))))))';
    is $Term2source($expectedTerm), $expectedLambda, "\$expectedTerm.lambda is $expectedLambda";

    my $time = now;
    $actualTerm = $Some2value($betaReduce($bigTerm)); #   $expectedTerm;    #   
    $time = (now.Real - $time.Real).round(0.2);
    diag "$time sec consumed for β-reduction";
    $actualLambda = $Term2source($actualTerm);
    is $Term-eq($actualTerm, $expectedTerm), '#true', "\$bigTerm reduces to $expectedLambda"
        or diag("exp: $expectedLambda\ngot: $actualLambda");
}


diag curryStats;