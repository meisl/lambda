use v6;
use Test;
use Test::Util_Term;
use Lambda::MaybeADT;
use Lambda::TermADT;
use Lambda::P6Currying;

# module under test:
use Lambda::BetaReduction;

plan 5;


#my $dc = $VarT('_');    # don't-care variable
my $g = $VarT('g');
my $h = $VarT('h');
my $k = $VarT('k');
my $u = $VarT('u');
my $v = $VarT('v');
my $x = $VarT('x');
my $y = $VarT('y');
my $z = $VarT('z');
my $c = $ConstT('c');


diag curryStats;

{ # (C (B (C cons) (C cons nil)))  =  (λa.λb.cons a (cons b nil))   # TODO: move to BetaReduction.t
    #my $s = $AppT(`'C', $AppT($AppT(`'B', $AppT(`'C', `'cons')), $AppT($AppT(`'C', `'cons'), `'nil')));
    my $C = $LamT('f', $LamT('a', $LamT('b', `'f b a')));  # use a,b instead of x,y to avoid need for α-conversion
    my $s = $AppT($C, $AppT($AppT(`'B', $AppT(`'C', `'cons')), $AppT($AppT(`'C', `'cons'), `'nil')));
    
    my $t = $LamT('a', $LamT('b', $AppT($AppT(`'cons', `'a'), $AppT($AppT(`'cons', `'b'), `'nil'))));
    diag '`(C (B (C cons) (C cons nil)))  =    ' ~ $Term2srcLess($s);
    diag '`(λa.λb.cons a (cons b nil))    =    ' ~ $Term2srcLess($t);

    my $s2 = $Some2value($betaReduce($s));
    my $t2 = $Some2value($betaReduce($t));

    diag '`(C (B (C cons) (C cons nil)))  =_β  ' ~ $Term2srcLess($s2);
    diag '`(λa.λb.cons a (cons b nil))    =_β  ' ~ $Term2srcLess($t2);

    is_eq($s2, $t2);
}


{ # first try with two minimal examples, as a sanity check:
    my ($t, $actual, $actualLambda);

    $t =`'x x';
    $actual = $betaReduce($t);
    is $actual, 'None', '`(x x) reduces to itself (sanity check)'
        or die;

    $t = `'(λx.x) x';   #$AppT($LamT('x', $x), $x);
    $actual = $Some2value($betaReduce($t));
    $actualLambda = $Term2source($actual);
    is_eq($actual, $x, "`({$Term2srcLesser($t)}) reduces to x (sanity check)")
        or die;
}


{ # profiling betaReduce
    my $time;
    
    $time = now;
    my $f1 = $VarT('f1');   # field 1
    my $f2 = $VarT('f2');   # field 2
    my $f3 = $VarT('f3');   # field 3
    my $f4 = $VarT('f4');   # field 4
    my $f5 = $VarT('f5');   # field 5

    my ( $bigTerm, $bigLambda, $expectedTerm, $expectedLambda, $actualTerm, $actualLambda);

    #$make-Ctor-chi_term: ctor2o4f5 (expects 4 callbacks and applies the 2nd to 5 fields)
    $bigTerm = $LamT('f1', $LamT('f2', $LamT('f3', $LamT('f4', $LamT('f5', $AppT($LamT('y', $LamT('_', $y)), $AppT($LamT('g', $LamT('h', $AppT($LamT('y', $LamT('_', $y)), $AppT($g, $h)))), $AppT($LamT('g', $LamT('h', $AppT($LamT('y', $LamT('_', $y)), $AppT($g, $h)))), $LamT('k', $AppT($AppT($LamT('k', $AppT($AppT($LamT('k', $AppT($AppT($LamT('k', $AppT($AppT($LamT('k', $AppT($AppT($LamT('x', $x), $k), $f1)), $k), $f2)), $k), $f3)), $k), $f4)), $k), $f5))))))))));
    diag (now.Real - $time.Real).round(0.3) ~ " sec consumed for big-term construction";

    $time = now;
    my $gh = $AppT($g, $h);
    my $Lx_x = $LamT('x', $x);
    my $λx_x = $LamT('x', $x);
    my $Ly_Ky = $LamT('y', $LamT('_', $y));
    # λf1.λf2.λf3.λf4.λf5.(λy.λ_.y) ((λg.λh.(λy.λ_.y) (g h)) ((λg.λh.(λy.λ_.y) (g h)) (λk.(λk.(λk.(λk.(λk.(λx.x) k f1) k f2) k f3) k f4) k f5)))
    $bigTerm = $LamT('f1', $LamT('f2', $LamT('f3', $LamT('f4', $LamT('f5', $AppT($Ly_Ky, $AppT($LamT('g', $LamT('h', $AppT($Ly_Ky, $gh))), $AppT($LamT('g', $LamT('h', $AppT($Ly_Ky, $gh))), $LamT('k', $AppT($AppT($LamT('k', $AppT($AppT($LamT('k', $AppT($AppT($LamT('k', $AppT($AppT($LamT('k', $AppT($AppT($λx_x, $k), $f1)), $k), $f2)), $k), $f3)), $k), $f4)), $k), $f5))))))))));
    diag (now.Real - $time.Real).round(0.3) ~ " sec consumed for big-term construction";

    $bigLambda = '(λf1.(λf2.(λf3.(λf4.(λf5.((λy.(λ_.y)) ((λg.(λh.((λy.(λ_.y)) (g h)))) ((λg.(λh.((λy.(λ_.y)) (g h)))) (λk.(((λk.(((λk.(((λk.(((λk.(((λx.x) k) f1)) k) f2)) k) f3)) k) f4)) k) f5))))))))))';
    is $Term2source($bigTerm), $bigLambda, "\$bigTerm.lambda is $bigLambda";
    diag $Term2srcLess($bigTerm);

    $expectedTerm = $LamT('f1', $LamT('f2', $LamT('f3', $LamT('f4', $LamT('f5', $LamT('_', $LamT('h', $LamT('_', $LamT('_', $AppT($AppT($AppT($AppT($AppT($h, $f1), $f2), $f3), $f4), $f5))))))))));
    # λf1.λf2.λf3.λf4.λf5.λ_.λh.λ_.λ_.h f1 f2 f3 f4 f5
    # λf1 f2 f3 f4 f5 _ h _ _.h f1 f2 f3 f4 f5
    $expectedLambda = '(λf1.(λf2.(λf3.(λf4.(λf5.(λ_.(λh.(λ_.(λ_.(((((h f1) f2) f3) f4) f5))))))))))';
    is $Term2source($expectedTerm), $expectedLambda, "\$expectedTerm.lambda is $expectedLambda";

    diag curryStats;

    $time = now;
    $actualTerm = $Some2value($betaReduce($bigTerm)); #   $expectedTerm;    #   
    diag (now.Real - $time.Real).round(0.2) ~ " sec consumed for β-reduction";
    $actualLambda = $Term2source($actualTerm);
    is $Term-eq($actualTerm, $expectedTerm), '#true', "\$bigTerm reduces to $expectedLambda"
        or diag("exp: $expectedLambda\ngot: $actualLambda");
    diag $Term2srcLess($actualTerm);
}


diag curryStats;
