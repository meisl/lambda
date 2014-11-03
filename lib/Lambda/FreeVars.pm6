use v6;

use Lambda::Base;
use Lambda::Boolean;
use Lambda::MaybeADT;
use Lambda::ListADT;
use Lambda::TermADT;

use Lambda::Conversion::Bool-conv;


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
            if convertTBool2P6Bool($is-ConstT($t)) {
                $false
            } elsif convertTBool2P6Bool($is-VarT($t)) {
                $VarT2name($t) eq $VarT2name($var) ?? $true !! $false
            } elsif convertTBool2P6Bool($is-AppT($t)) {
                $_or(
                    &self($var, $AppT2func($t)),
                    &self($var, $AppT2arg($t))
                )
            } elsif convertTBool2P6Bool($is-LamT($t)) {
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
            if convertTBool2P6Bool($is-ConstT($t)) {
                $false
            } elsif convertTBool2P6Bool($is-VarT($t)) {
                $false
            } elsif convertTBool2P6Bool($is-AppT($t)) {
                $_or(
                    &self($var, $binder, $AppT2func($t)),
                    &self($var, $binder, $AppT2arg($t))
                )
            } elsif convertTBool2P6Bool($is-LamT($t)) {
                my $vName    = $VarT2name($var);
                my $tVarName = $VarT2name($LamT2var($t));
                my $bName    = $VarT2name($binder);
                $_and(
                    convertP6Bool2TBool($tVarName ne $vName),     # if the λ binds the var then it's not free anywhere in the λ's body
                    $_if( convertP6Bool2TBool($bName eq $tVarName),     # or else, if the binder is the λ's var then...
                        { $is-free($var, $LamT2body($t)) },             # $var is free under $binder if $var is free in the λ's body
                        { &self($var, $binder, $LamT2body($t)) }        # otherwise it depends on the λ's body
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
            if convertTBool2P6Bool($is-ConstT($t)) {
                $None
            } elsif convertTBool2P6Bool($is-VarT($t)) {
                $_if( convertP6Bool2TBool($VarT2name($t) eq $name),
                    { $Some($t) },
                    { $None }
                )
            } elsif convertTBool2P6Bool($is-AppT($t)) {
                my $fromFunc = &self($name, $AppT2func($t));
                $_if( $is-Some($fromFunc),
                    { $fromFunc },
                    { &self($name, $AppT2arg($t)) }
                )
            } elsif convertTBool2P6Bool($is-LamT($t)) {
                $_if( convertP6Bool2TBool($VarT2name($LamT2var($t)) eq $name),
                    { $None },
                    { &self($name, $LamT2body($t)) }
                )
            } else {
                die "fell off type-dispatch with type " ~ $t.WHAT.perl
            }
        }
    }
));


constant $free-vars is export = $Y(lambdaFn(
    'free-vars', 
 q:to/ENDOFLAMBDA/,
    λself.λt.
        (case t
            (((ConstT val)    nil)
             ((VarT name)     (cons t nil)
             )
             ((AppT func arg) (let ((argFVs      (self arg))
                                    (argFVnames  (map VarT->name argFVs))
                                    (notInArgFVs (λe.let ((eName  (VarT->name e))
                                                          (found? (exists (λn.eq? eName n) argFVnames))
                                                         )
                                                   (not found)
                                                 )
                                    )
                                    (funcFVs     (filter notInArgFVs (self func)))
                                   )
                                (foldl (swap-args cons) argFVs funcFVs)
                              )
             )
             ((LamT var body) (let ((lbinder    (VarT->name var))
                                    (ne-binder? (λv.(not (eq? (VarT->name v) lbinder))))
                                    (bodyFVs    (self body)))
                                (filter ne-binder? bodyFVs)
                              )
             )
             (error (~ "unknown TTerm" (Term->Str t)))
           )
        )
ENDOFLAMBDA
    -> &self {
        -> TTerm $t {
            if convertTBool2P6Bool($is-ConstT($t)) {
                $nil;
            } elsif convertTBool2P6Bool($is-VarT($t)) {
                $cons($t, $nil);
            } elsif convertTBool2P6Bool($is-AppT($t)) {
                my $argFVs      = &self($AppT2arg($t));
                my $argFVnames  = $map($VarT2name, $argFVs);
                my $notInArgFVs = -> $e { 
                    my $eName = $VarT2name($e);
                    my $found =$exists(-> $n { convertP6Bool2TBool($eName eq $n) }, $argFVnames);
                    $not($found)
                };
                my $funcFVs     = $filter($notInArgFVs, &self($AppT2func($t)));
                $foldl($swap-args($cons), $argFVs, $funcFVs);
            } elsif convertTBool2P6Bool($is-LamT($t)) {
                my $lbName      = $VarT2name($LamT2var($t));
                my $isnt-binder = -> $e { convertP6Bool2TBool($VarT2name($e) ne $lbName) };
                my $bodyFVs     = &self($LamT2body($t));
                $filter($isnt-binder, $bodyFVs);
            } else {
                die "fell off type-dispatch with $t [:" ~ $t.WHAT.perl ~ ']';
            }
            
        }
    }
));
