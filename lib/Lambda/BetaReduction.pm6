use v6;

use Lambda::Base;
use Lambda::Boolean;
use Lambda::MaybeADT;
use Lambda::ListADT;
use Lambda::TermADT;
use Lambda::FreeVars;
use Lambda::Substitution;

use Lambda::Conversion::Bool-conv;


 # β-redex? - ie of form ((λx.B) z)
constant $is-betaRedex is export = lambdaFn(
    'betaRedex?',
q:to/ENDOFLAMBDA/,
    λt.case t ; TODO: case -> cascaded if
          (((ConstT val)    #false)
           ((VarT name)     #false)
           ((LamT var body) #false)
           ((AppT func arg)
               (LamT? func)
           )
          )
          (error (~ "unknown TTerm" (Term->Str t)))
ENDOFLAMBDA
    -> TTerm:D $t {
        if convertTBool2P6Bool($is-ConstT($t)) {
            $false
        } elsif convertTBool2P6Bool($is-VarT($t)) {
            $false
        } elsif convertTBool2P6Bool($is-LamT($t)) {
            $false
        } elsif convertTBool2P6Bool($is-AppT($t)) {
            # (P Q) is a β-redex if P is of form (λx.B).
            # If so, it β-contracts to [P/x] B, ie P substituted for x
            # in the λ's body but beware: any free var in P
            # must NOT be accidentally captured by a binding in B.
            # If that would be the case, we need to α-convert before.
            $is-LamT($AppT2func($t))
        } else {
            die "fell off type-dispatch with type " ~ $t.WHAT.perl
        }
    }
);


# either t is a β-redex or any child is betaReducible?
constant $is-betaReducible is export = $Y(lambdaFn(
    'betaReducible?',
q:to/ENDOFLAMBDA/,
    λself.λt._if (betaRedex? t)
                 (K #true)
                 (λ_.exists self (Term->children t))
ENDOFLAMBDA
    -> &self {
        -> TTerm $t {
            $_if( $is-betaRedex($t),
                { $true },
                { $exists(&self, $Term2children($t)) }
            )
            # self.isBetaRedex || ?self.children.map(*.isBetaReducible).any;
        }
    }
));


# one-step β-simplification (either of $t or any (one) child)
constant $betaContract is export = $Y(lambdaFn(
    'betaContract',
q:to/ENDOFLAMBDA/,
    λself.λt.
        case t ; TODO: case -> cascaded if
            (((ConstT val)    None)
             ((VarT name)     None)
             ((LamT var body)
                  (_if (betaReducible? body)
                       (K None)
                       (λ_.Some (LamT var (Some->value (self body))))
                  )
             )
             ((AppT func arg)
                  (_if (betaReducible? t)
                       (_if (betaRedex t)
                            (let ((forVar (LamT->var func))
                                  (inTerm (LamT->body func))
                                  (vName  (VarT->name forVar))
                                  (fvs    (filter
                                              (λv.not (eq? (VarT->name v) vName))
                                              (free-vars arg)
                                          )
                                  )
                                  (alpha-problematic (filter
                                                         (λv.free-under? forVar v inTerm)
                                                         fvs
                                                     )
                                  )
                                 )
                              (_if (nil? alpha-problematic)
                                   (let ((substituted-func (subst inTerm arg forVar))
                                         (isSame           (None? substituted-func))   ; TODO: check for Omega (may yield alpha-equiv term instead of None)
                                        )
                                     (_if isSame            ; TODO: use Maybe-or or something like that
                                          (λ_.Some inTerm)
                                          (K substituted-func)
                                     )
                                   )
                                   (λ_.error (~ "NYI: alpha-convert for " (List->Str alpha-problematic)))
                              )
                            )
                            (_if (betaReducible? func)
                                 (λ_.Some (AppT (Some->value (self func)) arg))
                                 (λ_.Some (AppT func (Some->value (self arg))))
                            )
                       )
                       (K None)
                  )
             )
            )
            (error (~ "unknown TTerm" (Term->Str t)))
ENDOFLAMBDA
    -> &self {
        -> TTerm $t {
            if convertTBool2P6Bool($is-ConstT($t)) {
                $None
            } elsif convertTBool2P6Bool($is-VarT($t)) {
                $None
            } elsif convertTBool2P6Bool($is-LamT($t)) {
                my $var  = $LamT2var($t);
                my $body = $LamT2body($t);
                $_if( $is-betaReducible($body),
                    { $Some($LamT($var, $Some2value(&self($body)))) },
                    { $None }
                )
            } elsif convertTBool2P6Bool($is-AppT($t)) {
                my $func = $AppT2func($t);
                my $arg  = $AppT2arg($t);
                $_if( $is-betaReducible($t),
                    { $_if( $is-betaRedex($t),
                          { my $forVar = $LamT2var($func);
                            my $inTerm = $LamT2body($func);
                            my $vName  = $VarT2name($forVar);
                            my $fvs = $filter(
                                -> $v { convertP6Bool2TBool($VarT2name($v) ne $vName) },
                                $free-vars($arg)
                            );
                            my $alpha-problematic = $filter(
                                -> $v { $is-free-under($forVar, $v, $inTerm) },
                                $fvs
                            );
                            $_if( $is-nil($alpha-problematic),
                                { 
                                    my $substituted-func = $subst($inTerm, $arg, $forVar);
                                    my $isSame = $is-None($substituted-func);   # TODO: check for Omega (may yield alpha-equiv term instead of None)
                                    # ($substituted-func.Str eq $t.Str) ?? $t !! $substituted-func;
                                    $_if( $isSame,   # TODO: use Maybe-or or something like that
                                        { $Some($inTerm) },
                                        { $substituted-func }
                                    )
                                },
                                { die "NYI: alpha-convert for " ~ $List2Str($alpha-problematic) }
                            )
                          },
                          { $_if( $is-betaReducible($func),
                                { $Some($AppT($Some2value(&self($func)), $arg)) },
                                { $Some($AppT($func, $Some2value(&self($arg)))) }
                            )
                          }
                      )
                    },
                    { $None }
                )
            } else {
                die "fell off type-dispatch with type " ~ $t.WHAT.perl
            }
        }
    }
));
