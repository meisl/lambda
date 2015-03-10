use v6;
use Test;
use Test::Util;
use Test::Util_Lambda;

use Lambda::Boolean;


# module under test:
use Lambda::ChurchNat;

plan 87;


# some abbreviations to make the tests more readable:
my $s = $chi-succ;

my $c0 = $chi0;
my $c1 = $chi1;
my $c2 = $chi2;
my $c3 = $chi3;
my $c4 = $chi4;
my $c5 = $chi5;
my $c6 = $chi6;
my $c7 = $chi7;
my $c8 = $chi8;
my $c9 = $chi9;


sub isFormal(::T, $n, $p6Name, $lambdaSymbol) {
    subtest({
        is_properLambdaFn($n, $lambdaSymbol);
        
        does_ok $n, T,  $lambdaSymbol;

    }, "$lambdaSymbol / $p6Name is formally a {T.perl}");
}


{ # χ0, χ1, χ2, ... are formally ChurchNat s ----------------------------------
    isFormal(TChurchNat, $c0, '$chi0', 'χ0');
    isFormal(TChurchNat, $c1, '$chi1', 'χ1');
    isFormal(TChurchNat, $c2, '$chi2', 'χ2');
    isFormal(TChurchNat, $c3, '$chi3', 'χ3');
    isFormal(TChurchNat, $c4, '$chi4', 'χ4');
    isFormal(TChurchNat, $c5, '$chi5', 'χ5');
    isFormal(TChurchNat, $c6, '$chi6', 'χ6');
    isFormal(TChurchNat, $c7, '$chi7', 'χ7');
    isFormal(TChurchNat, $c8, '$chi8', 'χ8');
    isFormal(TChurchNat, $c9, '$chi9', 'χ9');
}

{ # χ0, χ1, χ2, ... have pretty lambda expressions ----------------------------
    is $c0.lambda, '(λf.λx.x)', '$chi0.lambda';
    is $c1.lambda, '(λf.λx.(f x))', '$chi1.lambda';
    is $c2.lambda, '(λf.λx.(f (f x)))', '$chi2.lambda';
    is $c3.lambda, '(λf.λx.(f (f (f x))))', '$chi3.lambda';
    is $c4.lambda, '(λf.λx.(f (f (f (f x)))))', '$chi4.lambda';
    is $c5.lambda, '(λf.λx.(f (f (f (f (f x))))))', '$chi5.lambda';
    is $c6.lambda, '(λf.λx.(f (f (f (f (f (f x)))))))', '$chi6.lambda';
    is $c7.lambda, '(λf.λx.(f (f (f (f (f (f (f x))))))))', '$chi7.lambda';
    is $c8.lambda, '(λf.λx.(f (f (f (f (f (f (f (f x)))))))))', '$chi8.lambda';
    is $c9.lambda, '(λf.λx.(f (f (f (f (f (f (f (f (f x))))))))))', '$chi9.lambda';
}

{ # χ0? -----------------------------------------------------------------------
    isFormal(Callable, $is-chi0, '$is-chi0', 'χ0?');
    
    cmp_ok $is-chi0($c0), '===', $true,  'χ0? χ0';
    cmp_ok $is-chi0($c1), '===', $false, 'χ0? χ1';
    cmp_ok $is-chi0($c2), '===', $false, 'χ0? χ2';
    cmp_ok $is-chi0($c3), '===', $false, 'χ0? χ3';
    cmp_ok $is-chi0($c4), '===', $false, 'χ0? χ4';
    cmp_ok $is-chi0($c5), '===', $false, 'χ0? χ5';
    cmp_ok $is-chi0($c6), '===', $false, 'χ0? χ6';
    cmp_ok $is-chi0($c7), '===', $false, 'χ0? χ7';
    cmp_ok $is-chi0($c8), '===', $false, 'χ0? χ8';
    cmp_ok $is-chi0($c9), '===', $false, 'χ0? χ9';
}

{ # χsucc ---------------------------------------------------------------------
    isFormal(Callable, $chi-succ, '$chi-succ', 'χsucc');

    my sub test-succ($n-under-test, $equal-to, @unequal-to) {
        subtest {
            is $chi-succ($n-under-test).lambda, $equal-to.lambda, "(χsucc {$n-under-test}).lambda equals ({$equal-to}).lambda";
        
            for @unequal-to -> $k {
                isnt $chi-succ($n-under-test).lambda, $k.lambda, "(χsucc {$n-under-test}).lambda does NOT equal ($k).lambda";
            }
        }, "χsucc {$n-under-test}...";
    }

    # (succ n)
    test-succ($c0, $c1, [$c0,      $c2, $c3, $c4, $c5, $c6, $c7, $c8, $c9]);
    test-succ($c1, $c2, [$c0, $c1,      $c3, $c4, $c5, $c6, $c7, $c8, $c9]);
    test-succ($c2, $c3, [$c0, $c1, $c2,      $c4, $c5, $c6, $c7, $c8, $c9]);
    test-succ($c3, $c4, [$c0, $c1, $c2, $c3,      $c5, $c6, $c7, $c8, $c9]);
    test-succ($c4, $c5, [$c0, $c1, $c2, $c3, $c4,      $c6, $c7, $c8, $c9]);
    test-succ($c5, $c6, [$c0, $c1, $c2, $c3, $c4, $c5,      $c7, $c8, $c9]);
    test-succ($c6, $c7, [$c0, $c1, $c2, $c3, $c4, $c5, $c6,      $c8, $c9]);
    test-succ($c7, $c8, [$c0, $c1, $c2, $c3, $c4, $c5, $c6, $c7,      $c9]);
    test-succ($c8, $c9, [$c0, $c1, $c2, $c3, $c4, $c5, $c6, $c7, $c8     ]);

    # (succ (succ n))
    test-succ($s($c0), $c2,         [$c0, $c1,      $c3, $c4, $c5, $c6, $c7, $c8, $c9, $s($c9)]);
    test-succ($s($c1), $c3,         [$c0, $c1, $c2,      $c4, $c5, $c6, $c7, $c8, $c9, $s($c9)]);
    test-succ($s($c2), $c4,         [$c0, $c1, $c2, $c3,      $c5, $c6, $c7, $c8, $c9, $s($c9)]);
    test-succ($s($c3), $c5,         [$c0, $c1, $c2, $c3, $c4,      $c6, $c7, $c8, $c9, $s($c9)]);
    test-succ($s($c4), $c6,         [$c0, $c1, $c2, $c3, $c4, $c5,      $c7, $c8, $c9, $s($c9)]);
    test-succ($s($c5), $c7,         [$c0, $c1, $c2, $c3, $c4, $c5, $c6,      $c8, $c9, $s($c9)]);
    test-succ($s($c6), $c8,         [$c0, $c1, $c2, $c3, $c4, $c5, $c6, $c7,      $c9, $s($c9)]);
    test-succ($s($c7), $c9,         [$c0, $c1, $c2, $c3, $c4, $c5, $c6, $c7, $c8,      $s($c9)]);
    test-succ($s($c8), $s($c9),     [$c0, $c1, $c2, $c3, $c4, $c5, $c6, $c7, $c8, $c9         ]);
    test-succ($s($c9), $s($s($c9)), [$c0, $c1, $c2, $c3, $c4, $c5, $c6, $c7, $c8, $c9, $s($c9)]);
}

{ # the numerals as iterated function application -----------------------------
    my sub f(@arg) {
        return @(@arg.item, @arg.list);
    }
    my $out;

    my sub test(Int $n, TChurchNat:D $chi, Str:D $chiStr) {
        subtest({
            $out = $chi(&f, []);
            is($out.elems, $n, "($chiStr f x) calls f $n times")
                or diag($out.perl) and die;
            for 0..$n-1 -> $k {
                my $callNr = $k + 1;
                is($out[$n-$k-1].elems, $k, "($chiStr f x) applied f to (f^$k x) on call #$callNr")
                    or diag($out.perl) and die;
            }
        }, "($chiStr f x)...");
    }

    test(0, $c0, 'χ0');

    test(1,    $c1,         'χ1');
    test(1, $s($c0), '(χsucc χ0)');

    test(2,       $c2,                 'χ2');
    test(2,    $s($c1),         '(χsucc χ1)');
    test(2, $s($s($c0)), '(χsucc (χsucc χ0))');

    test(3,          $c3,                         'χ3');
    test(3,       $s($c2),                 '(χsucc χ2)');
    test(3,    $s($s($c1)),         '(χsucc (χsucc χ1))');
    test(3, $s($s($s($c0))), '(χsucc (χsucc (χsucc χ0)))');

    test(4,             $c4,                                 'χ4');
    test(4,          $s($c3),                         '(χsucc χ3)');
    test(4,       $s($s($c2)),                 '(χsucc (χsucc χ2))');
    test(4,    $s($s($s($c1))),         '(χsucc (χsucc (χsucc χ1)))');
    test(4, $s($s($s($s($c0)))), '(χsucc (χsucc (χsucc (χsucc χ0))))');

    test(5,                $c5,                                         'χ5');
    test(5,             $s($c4),                                 '(χsucc χ4)');
    test(5,          $s($s($c3)),                         '(χsucc (χsucc χ3))');
    test(5,       $s($s($s($c2))),                 '(χsucc (χsucc (χsucc χ2)))');
    test(5,    $s($s($s($s($c1)))),         '(χsucc (χsucc (χsucc (χsucc χ1))))');
    test(5, $s($s($s($s($s($c0))))), '(χsucc (χsucc (χsucc (χsucc (χsucc χ0)))))');

    test(6,                   $c6,                                                 'χ6');
    test(6,                $s($c5),                                         '(χsucc χ5)');
    test(6,             $s($s($c4)),                                 '(χsucc (χsucc χ4))');
    test(6,          $s($s($s($c3))),                         '(χsucc (χsucc (χsucc χ3)))');
    test(6,       $s($s($s($s($c2)))),                 '(χsucc (χsucc (χsucc (χsucc χ2))))');
    test(6,    $s($s($s($s($s($c1))))),         '(χsucc (χsucc (χsucc (χsucc (χsucc χ1)))))');
    test(6, $s($s($s($s($s($s($c0)))))), '(χsucc (χsucc (χsucc (χsucc (χsucc (χsucc χ0))))))');

    test(7,                      $c7,                                                         'χ7');
    test(7,                   $s($c6),                                                 '(χsucc χ6)');
    test(7,                $s($s($c5)),                                         '(χsucc (χsucc χ5))');
    test(7,             $s($s($s($c4))),                                 '(χsucc (χsucc (χsucc χ4)))');
    test(7,          $s($s($s($s($c3)))),                         '(χsucc (χsucc (χsucc (χsucc χ3))))');
    test(7,       $s($s($s($s($s($c2))))),                 '(χsucc (χsucc (χsucc (χsucc (χsucc χ2)))))');
    test(7,    $s($s($s($s($s($s($c1)))))),         '(χsucc (χsucc (χsucc (χsucc (χsucc (χsucc χ1))))))');
    test(7, $s($s($s($s($s($s($s($c0))))))), '(χsucc (χsucc (χsucc (χsucc (χsucc (χsucc (χsucc χ0)))))))');
}
