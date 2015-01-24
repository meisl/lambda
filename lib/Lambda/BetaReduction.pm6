use v6;

use Lambda::Base;
use Lambda::BaseP6;
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
                -> $_ { $true },
                -> $_ { $exists(&self, $Term2children($t)) }
            )
            # self.isBetaRedex || ?self.children.map(*.isBetaReducible).any;
        }
    }
));


constant $alpha-problematic-vars is export = lambdaFn(
    'alpha-problematic-vars',
q:to/ENDOFLAMBDA/,
    λt.case t ; TODO: case -> cascaded if
            (((ConstT val)    nil)
             ((VarT name)     nil)
             ((LamT var body) nil)
             ((AppT func arg)
                (_if (betaRedex? t)
                     (λ_.let ((var   (LamT->var  func))
                              (body  (LamT->body func))
                             )
                           (filter
                                ; no need to filter out var itself separately
                                ; since it cannot be free under itself in the body
                               (λv.free-under? var v body)
                               (free-vars arg)
                           )
                     )
                     (K nil)
                )
             )
            )
            (error (~ "unknown TTerm" (Term->Str t)))

ENDOFLAMBDA
    -> TTerm $t {
        $_if( $_or($is-ConstT($t), $_or($is-VarT($t), $is-LamT($t))),
            -> $_ { $nil },
            -> $_ { $_if( $is-AppT($t),
                        -> $_ { my $func = $AppT2func($t);
                                my $arg  = $AppT2arg($t);
                                $_if( $is-betaRedex($t),
                                    -> $_ { my $var   = $LamT2var($func);
                                        my $body  = $LamT2body($func);
                                        $filter(
                                            -> $v {
                                              # no need to filter out $var itself separately
                                              # since it cannot be free under itself in the body
                                              $is-free-under($var, $v, $body)
                                            },
                                            $free-vars($arg)
                                        );
                                    },
                                    -> $_ { $nil },
                                )
                        },
                        -> $_ { die "fell off type-dispatch with type " ~ $t.WHAT.perl }
                      )
            }
        )
    }
);


constant $alpha-needy-terms is export = $Y(lambdaFn(
    'alpha-needy-terms',
q:to/ENDOFLAMBDA/,
    λself.λt.λkeepfreevars.
        case t ; TODO: case -> cascaded if
             (((ConstT val)    nil)
              ((VarT name)     nil)
              ((AppT func arg) 
                (append (self func keepfreevars) (self arg keepfreevars))
              )
              ((LamT var body) nil)
             )
             (error (~ "unknown TTerm" (Term->Str t)))
ENDOFLAMBDA
    -> &self {
        -> TTerm $t, TList $keepfreevars {
            if convertTBool2P6Bool($is-ConstT($t)) {
                $nil;
            } elsif convertTBool2P6Bool($is-VarT($t)) {
                $nil;
            } elsif convertTBool2P6Bool($is-AppT($t)) {
                my $func = $AppT2func($t);
                my $arg  = $AppT2arg($t);
                $append(&self($func, $keepfreevars), &self($arg, $keepfreevars));
            } elsif convertTBool2P6Bool($is-LamT($t)) {
                my $var   = $LamT2var($t);
                my $vName = $VarT2name($var);
                my $body  = $LamT2body($t);
                my $fromBody = &self($body, $keepfreevars);
                $_if( $exists( -> $v { convertP6Bool2TBool($VarT2name($v) eq $vName) }, $keepfreevars),
                    -> $_ { $cons($t, $fromBody) },
                    -> $_ { $fromBody },
                );
            } else {
                die "fell off type-dispatch with type " ~ $t.WHAT.perl
            }
        }
    }
));


# one-step β-simplification (either of $t or any (one) child)
constant $betaContractXXX is export = $Y(lambdaFn(
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
                       (λ_._if (betaRedex t)
                               (λ_.let ((funcVar     (LamT->var func))
                                        (funcVarName (VarT->name funcVar))
                                        (_if (Ω? t)
                                             (λ_._if (eq? (VarT->name (LamT->var arg)) funcVarName)
                                                     (K None) ; func and arg are both literally the same ω
                                                     (λ_.Some (AppT arg arg)) ; otherwise one more step to make them so
                                             )
                                             (λ_.let ((funcBody          (LamT->body func))
                                                      (alpha-problematic (filter
                                                                             ; no need to filter out var itself separately
                                                                             ; since it cannot be free under itself in the body
                                                                             (λv.free-under? funcVar v funcBody)
                                                                             (free-vars arg)
                                                                         )
                                                      )
                                                     )
                                                   (_if (nil? alpha-problematic)
                                                        (λ_.let ((substituted-func (subst funcBody arg funcVar))
                                                                 (isSame           (None? substituted-func))
                                                                )
                                                              (_if isSame            ; TODO: use Maybe-or or something like that
                                                                   (λ_.Some funcBody)
                                                                   (K substituted-func)
                                                              )
                                                        )
                                                        (λ_.error (~ "NYI: alpha-convert for " (List->Str alpha-problematic)))
                                                   )
                                             )
                                        )
                                       )
                               )
                               (λ_._if (betaReducible? func)
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
                    -> $_ { $Some($LamT($var, $Some2value(&self($body)))) },
                    -> $_ { $None }
                )
            } elsif convertTBool2P6Bool($is-AppT($t)) {
                my $func = $AppT2func($t);
                my $arg  = $AppT2arg($t);
                $_if( $is-betaReducible($t),
                    -> $_ { $_if( $is-betaRedex($t),
                                -> $_ { my $funcVar  = $LamT2var($func);
                                    my $funcVarName = $VarT2name($funcVar);
                                    $_if( $is-Omega($t),
                                        -> $_ { $_if( convertP6Bool2TBool($VarT2name($LamT2var($arg)) eq $funcVarName),
                                                    -> $_ { $None }, # func and arg are both the (literally) same omega
                                                    -> $_ { $Some($AppT($arg, $arg)) }  # otherwise one more step to make them so
                                                )
                                        },
                                        -> $_ { my $funcBody  = $LamT2body($func);
                                                my $alpha-problematic = $filter(
                                                    # no need to filter out $var itself separately
                                                    # since it cannot be free under itself in the body
                                                    -> $v { $is-free-under($funcVar, $v, $funcBody) },
                                                    $free-vars($arg)
                                                );
                                                $_if( $is-nil($alpha-problematic),
                                                    -> $_ { my $substituted-func = $subst($funcBody, $arg, $funcVar);
                                                        my $isSame = $is-None($substituted-func);
                                                        $_if( $isSame,   # TODO: use Maybe-or or something like that
                                                            -> $_ { $Some($funcBody) },
                                                            -> $_ { $substituted-func }
                                                        )
                                                    },
                                                    -> $_ { die "NYI: alpha-convert for " ~ $List2Str($alpha-problematic) }
                                                )
                                        }
                                    );
                                },
                                -> $_ { $_if( $is-betaReducible($func),
                                            -> $_ { $Some($AppT($Some2value(&self($func)), $arg)) },
                                            -> $_ { $Some($AppT($func, $Some2value(&self($arg)))) }
                                        )
                                }
                            )
                    },
                    -> $_ { $None }
                )
            } else {
                die "fell off type-dispatch with type " ~ $t.WHAT.perl
            }
        }
    }
));

my constant $K1None = $K($None);
my constant $liftedCtor2 = lambdaFn(
    Str, 'λctor.λa1.λtransform2nd.λa2.let ((a2-transformed (transform2nd a2))) if (None? a2-transformed) None (Some (ctor a1 (Some->value a2-transformed)))',
    -> &ctor, TTerm $a1, &transform2nd, TTerm $a2 {
        my $a2transformed = &transform2nd($a2);
        $_if( $is-None($a2transformed),
            $K1None,
            -> Mu { $Some(&ctor($a1, $Some2value($a2transformed))) }
        )
    }
);


# one-step β-simplification (either of $t or any (one) child)
constant $betaContract is export = $Y(lambdaFn(
    'betaContract', 'not yet implemented',
    -> &self {
        -> TTerm $t {
            $destruct-Term($t,
                # t is VarT
                $K1None,

                # t is AppT
                -> TTerm $func, TTerm $arg {
                    $destruct-Term($func,
                        # func is VarT
                        -> Mu { $liftedCtor2($AppT, $func, &self, $arg) },
                        
                        # func is AppT
                        -> Mu, Mu {
                            my $func2 = &self($func);
                            $_if( $is-Some($func2),
                                -> Mu { $Some($AppT($Some2value($func2), $arg)) },
                                -> Mu { $liftedCtor2($AppT, $func, &self, $arg) }
                            )
                        },
                        
                        # func is LamT
                        -> $funcVar, $funcBody {    # so t is a beta-redex
                            my $alpha-problematic = $filter(
                                # no need to filter out $var itself separately
                                # since it cannot be free under itself in the body
                                -> $v { $is-free-under($funcVar, $v, $funcBody) },
                                $free-vars($arg)
                            );
                            $_if( $is-nil($alpha-problematic),
                                -> Mu {
                                    my $substituted-func = $subst($funcBody, $arg, $funcVar);
                                    my $isSame = $is-None($substituted-func);
                                    $_if( $isSame,   # TODO: use Maybe-or or something like that
                                        -> Mu { $Some($funcBody) },
                                        -> Mu {
                                            my $K1substituted-func = $K($substituted-func);
                                            $_if( $is-selfAppOfVar($funcVar, $funcBody),    # is t (literal Omega?) / pt 1
                                                -> Mu {
                                                    $on-LamT(   # is t (literal Omega?) / pt 2
                                                        -> TTerm $argVar, TTerm $argBody {
                                                            $_if( $is-selfAppOfVar($funcVar, $argBody),    # should be *literal* Omega
                                                                $K1None, # func and arg are both the (literally) same omega
                                                                $K1substituted-func  # otherwise one more step to make them so
                                                            )
                                                        } does lambda("λargVar.λargBody.if (selfAppOfVar? funcVar argBody) (K None) (K1substituted-func)"),
                                                        $K1substituted-func,
                                                        $arg
                                                    )
                                                },
                                                $K1substituted-func
                                            )
                                        }
                                    )
                                },
                                -> Mu { die "NYI: alpha-convert for " ~ $List2Str($alpha-problematic) }
                            )
                        },
                        
                        # func is ConstT
                        -> Mu { $liftedCtor2($AppT, $func, &self, $arg) }
                    )
                },

                # t is LamT
                -> TTerm $var, TTerm $body {
                    $liftedCtor2($LamT, $var, &self, $body)
                },

                # t is ConstT
                $K1None
            )
        }
    }
));


# betaReduce: β-contract until fixed-point (Ω is considered a fixed-point, too)

# Main reason for returning a Maybe (rather than eg the same Term if nothing changes)
# is that we don't need to compare terms for equality then.
constant $betaReduce is export = lambdaFn(
    'betaReduce',
q:to/ENDOFLAMBDA/,
    λt.(findFP
         (λx.None?)
         (Maybe-lift-in betaContract)
         (betaContract t)
       )
ENDOFLAMBDA
    -> TTerm $t {
        $findFP(
            -> $x, TMaybe:D $y { $is-None($y) },
            $Maybe-lift-in($betaContract),
            $betaContract($t)
        );
    }
);