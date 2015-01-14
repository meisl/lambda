use v6;

use Lambda::BaseP6;
use Lambda::Boolean;
use Lambda::ChurchNat;

module Lambda::Projections;



my constant $myI = lambdaFn(
    Str, 'λx.x',
    -> $x { $x }
);

my constant $myK = lambdaFn(
    Str, 'λx.λ_.x',
    -> $x { 
        lambdaFn(Str, "λ_.{$x.lambda.substr(1, *-1)}", 
            lambdaFn( Str, $x.lambda, -> Mu { $x } )
        )
    }
);

my constant $myL = lambdaFn(    # = B K
    Str, 'λf.λx.λ_.f x',
    -> $f {
        $f === $myI
            ?? $myK
            !! lambdaFn(
                   Str, "λy.λ_.{$f.lambda} y", 
                   -> $x {
                       $myK($f($x)) 
                   }
               )
    }
);

constant $make-pi is export = lambdaFn(
    'make-π', 'λignore-left.λignore-right.ignore-right.λf K (ignore-left (B K) f)',
    -> TChurchNat $ignore-left, TChurchNat $ignore-right, $f {
        $ignore-right($myK, $ignore-left($myL, $f))
    }
);

#my $h = $myI;
my $h = lambdaFn(Str, 'λh.h a b c', -> $x { $x });

my $pi1to1 = $make-pi($chi0, $chi0, $h);
say $pi1to1.lambda;
say '';

my $pi2to1 = $make-pi($chi0, $chi1, $h);
my $pi2to2 = $make-pi($chi1, $chi0, $h);
say $pi2to1.lambda;
say $pi2to2.lambda;
say '';

my $pi3to1 = $make-pi($chi0, $chi2, $h);
my $pi3to2 = $make-pi($chi1, $chi1, $h);
my $pi3to3 = $make-pi($chi2, $chi0, $h);
say $pi3to1.lambda;
say $pi3to2.lambda;
say $pi3to3.lambda;
say '';

my $pi4to1 = $make-pi($chi0, $chi3, $h);
my $pi4to2 = $make-pi($chi1, $chi2, $h);
my $pi4to3 = $make-pi($chi2, $chi1, $h);
my $pi4to4 = $make-pi($chi3, $chi0, $h);
say $pi4to1.lambda;
say $pi4to2.lambda;
say $pi4to3.lambda;
say $pi4to4.lambda;
say '';
