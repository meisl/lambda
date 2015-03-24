use v6;
use Test;
use Test::Util_Term;
use Lambda::MaybeADT;
use Lambda::TermADT;
use Lambda::P6Currying;

# module under test:
use Lambda::BetaReduction;

plan 7;


my $time;

diag curryStats;

{ # (C (B (C cons) (C cons nil)))  =  (λa.λb.cons a (cons b nil))   # TODO: move to BetaReduction.t
    subtest({ # this one does not need alpha-conversion (first C uses binders a,b instead of x,y)
        my $C = $LamT('f', $LamT('a', $LamT('b', `'f b a')));
        my $s = $AppT($C, $AppT($AppT(`'B', $AppT(`'C', `'cons')), $AppT($AppT(`'C', `'cons'), `'nil')));
        
        my $t = $LamT('a', $LamT('b', $AppT($AppT(`'cons', `'a'), $AppT($AppT(`'cons', `'b'), `'nil'))));
        diag '`(C (B (C cons) (C cons nil)))  =    ' ~ $Term2srcLess($s);
        diag '`(λa.λb.cons a (cons b nil))    =    ' ~ $Term2srcLess($t);

        $time = now;
        my $s2 = $Some2value($betaReduce($s));
        my $t2 = $Some2value($betaReduce($t));
        diag (now.Real - $time.Real).round(0.01) ~ " sec consumed for beta-reduction";

        diag '`(C (B (C cons) (C cons nil)))  =_β  ' ~ $Term2srcLess($s2);
        diag '`(λa.λb.cons a (cons b nil))    =_β  ' ~ $Term2srcLess($t2);

        is_eq($s2, $t2);
    }, '`(C (B (C cons) (C cons nil)))  =_β  `(λa.λb.cons a (cons b nil))  [no alpha-conv]');
    
    subtest({ # this one does require alpha-conversion
        my $s = $AppT(`'C', $AppT($AppT(`'B', $AppT(`'C', `'cons')), $AppT($AppT(`'C', `'cons'), `'nil')));
        
        my $t = $LamT('x', $LamT('y', $AppT($AppT(`'cons', `'x'), $AppT($AppT(`'cons', `'y'), `'nil'))));
        diag '`(C (B (C cons) (C cons nil)))  =    ' ~ $Term2srcLess($s);
        diag '`(λx.λy.cons x (cons y nil))    =    ' ~ $Term2srcLess($t);

        $time = now;
        my $s2 = $Some2value($betaReduce($s));
        my $t2 = $Some2value($betaReduce($t));
        diag (now.Real - $time.Real).round(0.01) ~ " sec consumed for beta-reduction";

        diag '`(C (B (C cons) (C cons nil)))  =_β  ' ~ $Term2srcLess($s2);
        diag '`(λx.λy.cons x (cons y nil))    =_β  ' ~ $Term2srcLess($t2);

        is_eq($s2, $t2);
    }, '`(C (B (C cons) (C cons nil)))  =_β  `(λx.λy.cons x (cons y nil))  [needs alpha-conv]');

}


{ # first try with two minimal examples, as a sanity check:
    my ($t, $actual);

    $t =`'x x';
    $actual = $betaReduce($t);
    is $actual, 'None', '`(x x) reduces to itself (sanity check)'
        or die;

    $t = `'(λx.x) x';
    $actual = $Some2value($betaReduce($t));
    is_eq($actual, `'x', "`({$Term2srcLesser($t)}) reduces to x (sanity check)")
        or die;
}


{ # profiling betaReduce
    my ( $bigTerm, $bigLambda, $expectedTerm, $expectedLambda, $actualTerm);

    #$make-Ctor-chi_term: ctor2o4f5 (expects 4 callbacks and applies the 2nd to 5 fields)
    $bigLambda = 'λf1.λf2.λf3.λf4.λf5.(λy.λ_.y) ((λg.λh.(λy.λ_.y) (g h)) ((λg.λh.(λy.λ_.y) (g h)) (λk.(λk.(λk.(λk.(λk.(λx.x) k f1) k f2) k f3) k f4) k f5)))';
    $time = now;
    $bigTerm = $LamT('f1', $LamT('f2', $LamT('f3', $LamT('f4', $LamT('f5', $AppT(`'λy.λ_.y', $AppT(`'λg.λh.(λy.λ_.y) (g h)', $AppT(`'λg.λh.(λy.λ_.y) (g h)', $LamT('k', $AppT($AppT($LamT('k', $AppT($AppT($LamT('k', $AppT($AppT($LamT('k', $AppT($AppT(`'λk.(λx.x) k f1', `'k'), `'f2')), `'k'), `'f3')), `'k'), `'f4')), `'k'), `'f5'))))))))));
    diag (now.Real - $time.Real).round(0.01) ~ " sec consumed for big-term construction";

    is $Term2srcLess($bigTerm), $bigLambda, "\$bigTerm.lambda is $bigLambda";

    $expectedTerm = $LamT('f1', $LamT('f2', $LamT('f3', $LamT('f4', $LamT('f5', $LamT('_', $LamT('h', $LamT('_', $LamT('_', `'h f1 f2 f3 f4 f5')))))))));
    $expectedLambda = 'λf1.λf2.λf3.λf4.λf5.λ_.λh.λ_.λ_.h f1 f2 f3 f4 f5';
    is $Term2srcLess($expectedTerm), $expectedLambda, "\$expectedTerm.lambda is $expectedLambda";

    diag curryStats;

    $time = now;
    $actualTerm = $Some2value($betaReduce($bigTerm));
    diag (now.Real - $time.Real).round(0.01) ~ " sec consumed for β-reduction";
    is_eq($actualTerm, $expectedTerm, '$bigTerm reduces to $expectedTerm');
}


diag curryStats;
