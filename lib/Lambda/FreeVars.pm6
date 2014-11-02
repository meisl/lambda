use v6;

use Lambda::Base;
use Lambda::Boolean;
use Lambda::MaybeADT;
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
        -> TTerm $var, TTerm $t {
            if $is-ConstT($t) === $true {
                $false
            } elsif $is-VarT($t) === $true {
                $VarT2name($t) eq $VarT2name($var) ?? $true !! $false
            } elsif $is-AppT($t) === $true {
                $_or(
                    &self($var, $AppT2func($t)),
                    &self($var, $AppT2arg($t))
                )
            } elsif $is-LamT($t) === $true {
                $_and(
                    $VarT2name($LamT2var($t)) ne $VarT2name($var) ?? $true !! $false,
                    &self($var, $LamT2body($t))
                )
            } else {
                die "fell off type-dispatch with type " ~ $t.WHAT.perl
            }
        }
    }
));

constant $is-free-under is export = $Y(lambdaFn(
    'free-under?', 
 q:to/ENDOFLAMBDA/,
    λself.λvar.λbinder.λt.
        (case t ; TODO: case -> cascaded if
            (((ConstT val)    #false)
             ((VarT name)     #false)
             ((AppT func arg) (_or (self var binder func) (self var binder arg)))
             ((LamT v body)   (let ((vName  (VarT->name var))
                                    (bName  (VarT->name binder))
                                    (lbName (VarT->name v)))
                                (_and
                                  (not (eq? lbName vName))
                                  (_if (eq? lbName bName)
                                    (free? var body)
                                    (self var binder body)
                                  )
                                )
                              )
             )
            )
            (error (~ "unknown TTerm" (Term->Str t)))
        )
ENDOFLAMBDA
    -> &self {
        -> TTerm $var, TTerm $binder, TTerm $t {
            if $is-ConstT($t) === $true {
                $false
            } elsif $is-VarT($t) === $true {
                $$false
            } elsif $is-AppT($t) === $true {
                $_or(
                    &self($var, $binder, $AppT2func($t)),
                    &self($var, $binder, $AppT2arg($t))
                )
            } elsif $is-LamT($t) === $true {
                my $vName    = $VarT2name($var);
                my $tVarName = $VarT2name($LamT2var($t));
                my $bName    = $VarT2name($binder);
                $_and(
                    $tVarName ne $vName ?? $true !! $false,     # if the λ binds the var then it's not free anywhere in the λ's body
                    $_if( $bName eq $tVarName ?? $true !! $false,   # or else, if the binder is the λ's var then...
                        { $is-free($var, $LamT2body($t)) },         # $var is free under $binder if $var is free in the λ's body
                        { &self($var, $binder, $LamT2body($t)) }    # otherwise it depends on the λ's body
                    )
                );
            } else {
                die "fell off type-dispatch with type " ~ $t.WHAT.perl
            }
        }
    }
));


constant $free-var is export = $Y(lambdaFn(
    'free-var', 
 q:to/ENDOFLAMBDA/,
    λself.λname.λt.
        (case t
            (((ConstT val)    None)
             ((VarT tName)    (_if (eq? name tName)
                                (λ_.Some t)
                                (λ_.None)
                              )
             )
             ((AppT func arg) (let ((fromFunc (self name func))
                                    (inFunc?  (Some? fromFunc))
                                   )
                                (_if inFunc?
                                  fromFunc
                                  (self name arg)
                                )
                              )
             
             )
             ((LamT v body)   (_if (eq? name (VarT->name v))
                                (λ_.None)
                                (λ_.self name body)
                              )
            )
            (error (~ "unknown TTerm" (Term->Str t)))
           )
        )
ENDOFLAMBDA
    -> &self {
        -> Str:D $name, TTerm $t {
            if $is-ConstT($t) === $true {
                $None
            } elsif $is-VarT($t) === $true {
                $_if( $VarT2name($t) eq $name ?? $true !! $false,
                    { $Some($t) },
                    { $None }
                )
            } elsif $is-AppT($t) === $true {
                my $fromFunc = &self($name, $AppT2func($t));
                $_if( $is-Some($fromFunc),
                    { $fromFunc },
                    { &self($name, $AppT2arg($t)) }
                )
            } elsif $is-LamT($t) === $true {
                $_if( $VarT2name($LamT2var($t)) eq $name ?? $true !! $false,
                    { $None },
                    { &self($name, $LamT2body($t)) }
                )
            } else {
                die "fell off type-dispatch with type " ~ $t.WHAT.perl
            }
        }
    }
));