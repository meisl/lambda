use v6;
use Test;
use Test::Util_Term;
use Lambda::MaybeADT;
use Lambda::TermADT;
use Lambda::PairADT;

use Lambda::Base;
use Lambda::BaseP6;
use Lambda::P6Currying;
use Lambda::Conversion;

# module under test:
use Lambda::BetaReduction;

plan 7;


my $time;

diag curryStats;

my $fpSearch = $findFP-inMaybe(lambdaFn('betaContract', 'λt.error "NYI"', -> TPair $pair {
    my $n = $fst($pair);
    my $term = $snd($pair);
    diag sprintf('    =_β%-2d  %s', $n, $Term2srcLess($term));
    case-Maybe($betaContract($term),
        None => $None,
        Some => -> $v { $Some($Pair($n+1, $v)) }
    );
}));

my $reduce = -> TTerm $start {
    my $startPair = $Pair(0, $start);
    case-Maybe($fpSearch($startPair),
        None => {
            diag '    (0 steps)';
            $None;
        },
        Some => -> $pair {
            diag "    ({$fst($pair)} steps)";
            $Some($snd($pair));
        }
    );
}


## will diverge:
#$reduce(`'Y');
#diag curryStats;
#exit;


## uncomment to disable debug diagnostics:
#$reduce = $betaReduce;

sub is_confluent(TTerm $s, TTerm $t, Str :$msg = '', Str :$sStr, Str :$tStr) {
    my $sSrc = $Term2srcLess($s);
    my $tSrc = $Term2srcLess($t);
    my $timeStr;
#    subtest({
        diag("$sStr  =  $sSrc") if $sStr.defined;
        my $timeS = now;
        my $sr = case-Maybe($reduce($s), None => $s, Some => $I);
        $timeS = (now - $timeS).Real;

        diag("$tStr  =  $tSrc") if $tStr.defined;
        my $timeT = now;
        my $tr = case-Maybe($reduce($t), None => $t, Some => $I);
        $timeT = (now - $timeT).Real;

        my $timeTtl = max($timeS + $timeT, 0.001);
        $timeStr = sprintf('%1.2f = %1.2f + %1.2f sec (%1.0f%% + %1.0f%%) consumed for beta-reduction',
            $timeTtl, 
            $timeS,  $timeT,
            $timeS / $timeTtl * 100, $timeT / $timeTtl * 100
        );
        diag $timeStr;

        is_eq-Term($sr, $tr, "{$sStr // $sSrc}  =_β*  {$tStr // $tSrc}  $msg");
#    });
}

{ # TODO: move to BetaReduction.t
    is_confluent( # this one does not need alpha-conversion (first C uses binders a,b instead of x,y)
        $AppT(`'λf.λa.λb.f b a', `'B (C cons) (C cons nil)'),   :sStr('(λf.λa.λb.f b a) (B (C cons) (C cons nil))'),
        `'λa.λb.cons a (cons b nil)',                           :tStr('λa.λb.cons a (cons b nil)'),
        msg => '[NO alpha-conv needed]'
    );

    is_confluent( # this one DOES require alpha-conversion
        $AppT(`'C', `'B (C cons) (C cons nil)'),    :sStr('(C (B (C cons) (C cons nil)))'),
        `'λx.λy.cons x (cons y nil)',               :tStr('λx.λy.cons x (cons y nil)'),
        msg => '[DOES need alpha-conv]'
    );
}


{ # first try with two minimal examples, as a sanity check:
    is_confluent(`'x x',      `'x x', msg => '(sanity check)');
    is_confluent(`'(λx.x) x', `'x',   msg => '(sanity check)');
}


{ # profiling betaReduce
    my ($bigTerm, $bigLambda, $expectedTerm, $expectedLambda);

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

    is_confluent($bigTerm, $expectedTerm);
}


diag curryStats;
