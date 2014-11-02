use v6;

use Lambda::Base;
use Lambda::Boolean;
use Lambda::TermADT;

constant $is-free is export = $Y(lambdaFn(
    'free?', 
 q:to/ENDOFLAMBDA/,
    λself.λvar.λt.
        (case t
            (((ConstT val)    #false)
             ((VarT name)     (eq? name (VarT->name var)))
             ((AppT func arg) (_or (self var func) (self var arg)))
             ((LamT v body)   (_and (not (eq? v var)) (self var body)))
            )
            (error (~ "unknown TTerm" (Term->Str t)))
        )
ENDOFLAMBDA
    -> &self {
        -> TTerm $var, TTerm $in {
            if $is-ConstT($in) === $true {
                $false
            } elsif $is-VarT($in) === $true {
                $VarT2name($in) eq $VarT2name($var) ?? $true !! $false
            } elsif $is-AppT($in) === $true {
                $_or(
                    &self($var, $AppT2func($in)),
                    &self($var, $AppT2arg($in))
                )
            } elsif $is-LamT($in) === $true {
                $_and(
                    $VarT2name($LamT2var($in)) ne $VarT2name($var) ?? $true !! $false,
                    &self($var, $LamT2body($in))
                )
            } else {
                die "fell off type-dispatch with type " ~ $in.WHAT.perl
            }
        }
    }
));
