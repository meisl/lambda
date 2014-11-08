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
            { $nil },
            { $_if( $is-AppT($t),
                  { my $func = $AppT2func($t);
                    my $arg  = $AppT2arg($t);
                    $_if( $is-betaRedex($t),
                        { my $var   = $LamT2var($func);
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
                        { $nil },
                    )
                  },
                  { die "fell off type-dispatch with type " ~ $t.WHAT.perl }
              )
            }
        )
    }
);

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
                    { $Some($LamT($var, $Some2value(&self($body)))) },
                    { $None }
                )
            } elsif convertTBool2P6Bool($is-AppT($t)) {
                my $func = $AppT2func($t);
                my $arg  = $AppT2arg($t);
                $_if( $is-betaReducible($t),
                    { $_if( $is-betaRedex($t),
                          { my $funcVar  = $LamT2var($func);
                            my $funcVarName = $VarT2name($funcVar);
                            $_if( $is-Omega($t),
                                { $_if( convertP6Bool2TBool($VarT2name($LamT2var($arg)) eq $funcVarName),
                                      { $None }, # func and arg are both the (literally) same omega
                                      { $Some($AppT($arg, $arg)) }  # otherwise one more step to make them so
                                  )
                                },
                                { my $funcBody  = $LamT2body($func);
                                  my $alpha-problematic = $filter(
                                      # no need to filter out $var itself separately
                                      # since it cannot be free under itself in the body
                                      -> $v { $is-free-under($funcVar, $v, $funcBody) },
                                      $free-vars($arg)
                                  );
                                  $_if( $is-nil($alpha-problematic),
                                      { my $substituted-func = $subst($funcBody, $arg, $funcVar);
                                        my $isSame = $is-None($substituted-func);
                                        $_if( $isSame,   # TODO: use Maybe-or or something like that
                                            { $Some($funcBody) },
                                            { $substituted-func }
                                        )
                                      },
                                      { die "NYI: alpha-convert for " ~ $List2Str($alpha-problematic) }
                                  )
                                }
                            );
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