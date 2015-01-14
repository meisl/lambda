use v6;

use Lambda::BaseP6;
use Lambda::Boolean;

module Lambda::ChurchNat;



# data ChurchNat = χZero
#                | χSucc ChurchNat
my role TChurchNat is export {
}


constant $chi-succ is export = lambdaFn(
    'χsucc', 'λn.λf.λx.n f (f x)',      # f (n f x)
    -> TChurchNat:D $n -->TChurchNat{
        my $nLambda = $n.lambda;
        my $fStr    = $nLambda.substr(2, 1);
        my $lambdaExpr = "λ{$fStr}.λx.({$fStr} {$nLambda.substr(7)}";
        lambdaFn(
            Str, $lambdaExpr,
            -> $f {
                my $n-f = $n($f);
                my $fStr = $f.?symbol // $f.?lambda // $f.gist;
                lambdaFn(
                    Str, "λx.({$fStr} {$n-f.lambda.substr(4)}",
                    -> $x { $f($n($f, $x)) }    # $n($f, $f($x)) }  #   
                )
            }
        ) does TChurchNat
    }
);

constant $chi0 is export = lambdaFn(
    'χ0', 'λf.λx.x',
    -> $f {
        lambdaFn(
            Str, 'λx.x',
            -> $x { $x }
        )
    }
) does TChurchNat;

constant $chi1 is export = $chi-succ($chi0) does Definition(:symbol('χ1'));
constant $chi2 is export = $chi-succ($chi1) does Definition(:symbol('χ2'));
constant $chi3 is export = $chi-succ($chi2) does Definition(:symbol('χ3'));
constant $chi4 is export = $chi-succ($chi3) does Definition(:symbol('χ4'));
constant $chi5 is export = $chi-succ($chi4) does Definition(:symbol('χ5'));
constant $chi6 is export = $chi-succ($chi5) does Definition(:symbol('χ6'));
constant $chi7 is export = $chi-succ($chi6) does Definition(:symbol('χ7'));
constant $chi8 is export = $chi-succ($chi7) does Definition(:symbol('χ8'));
constant $chi9 is export = $chi-succ($chi8) does Definition(:symbol('χ9'));


constant $is-chi0 is export = lambdaFn(
    'χ0?', 'λn.n (K #false) #true',
    -> $n { $n(-> Mu { $false }, $true) }
);
