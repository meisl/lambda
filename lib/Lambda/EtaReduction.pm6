use v6;

use Lambda::Base;
use Lambda::Boolean;
use Lambda::MaybeADT;
use Lambda::ListADT;
use Lambda::TermADT;
use Lambda::FreeVars;

use Lambda::Conversion::Bool-conv;


# η-redex? - ie of form λx.(B x) where x not free in B
constant $is-etaRedex is export = lambdaFn(
    'etaRedex?', 
q:to/ENDOFLAMBDA/,
    λt.case t ; TODO: case -> cascaded if
          (((ConstT val)    #false)
           ((VarT name)     #false)
           ((AppT func arg) #false)
           ((LamT v body)             ; λx.(B x) is an η-redex if x not free in B
               (_if (AppT? body)      ; (if so, it η-contracts to just B)
                   (λ_.let ((func (AppT->func body))
                            (arg  (AppT->arg body))
                           )
                         (_if (VarT? arg)
                              (λ_.(_if (eq? (VarT->name arg) (VarT->name v))
                                       (λ_.not (free? v func))
                                       (K #false)
                                  )
                              )
                              (K #false)
                         )
                   )
                   (K #false)
               )
           )
          )
          (error (~ "unknown TTerm" (Term->Str t)))
ENDOFLAMBDA
    -> TTerm:D $t {
        if convertTBool2P6Bool($is-ConstT($t)) {
            $false
        } elsif convertTBool2P6Bool($is-VarT($t)) {
            $false
        } elsif convertTBool2P6Bool($is-AppT($t)) {
            $false
        } elsif convertTBool2P6Bool($is-LamT($t)) {
            # λx.(B x) is an η-redex if x not free in B.
            # (if so, it η-contracts to just B)
            my $var  = $LamT2var($t);
            my $body = $LamT2body($t);
            $_if( $is-AppT($body),
                { my $func = $AppT2func($body);
                  my $arg  = $AppT2arg($body);
                  $_if( $is-VarT($arg),
                    { $_if( convertP6Bool2TBool($VarT2name($arg) eq $VarT2name($var)),
                          { $not($is-free($var, $func)) },
                          { $false }
                      )
                    },
                    { $false }
                  )
                },
                { $false }
            );
        } else {
            die "fell off type-dispatch with type " ~ $t.WHAT.perl
        }
    }
);


# either t is an η-redex or any child is etaReducible?
constant $is-etaReducible is export = $Y(lambdaFn(
    'etaReducible?',
q:to/ENDOFLAMBDA/,
    λself.λt._if (etaRedex? t)
                 (K #true)
                 (λ_.exists self (Term->children t))
ENDOFLAMBDA
    -> &self {
        -> TTerm $t {
            $_if( $is-etaRedex($t),
                { $true },
                { $exists(&self, $Term2children($t)) }
            )
            # self.isEtaRedex || ?self.children.map(*.isEtaReducible).any;
        }
    }
));


# etaContract: one-step η-simplification, either of η-redex itself or any (one) child

# Main reason for returning a Maybe (rather than eg the same Term if nothing changes)
# is that we don't need to compare terms for equality then.
constant $etaContract is export = $Y(lambdaFn(
    'etaContract',
q:to/ENDOFLAMBDA/,
    λself.λt.
        case t ; TODO: case -> cascaded if
            (((ConstT val)    None)
             ((VarT name)     None)
             ((AppT func arg)
                (_if (etaReducible? func)
                     (λ_.Some (AppT (Some->value (self func)) arg))
                     (_if (etaReducible? arg)
                          (λ_.Some (AppT func (Some->value (self arg))))
                          (K None)
                     )
                )
             )
             ((LamT var body)
                (_if (etaRedex? t)
                     (λ_.Some (AppT->func body))
                     (_if (etaReducible? body)
                          (λ_.Some (LamT var (Some->value (self body))))
                          (K None)
                     )
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
            } elsif convertTBool2P6Bool($is-AppT($t)) {
                my $func = $AppT2func($t);
                my $arg  = $AppT2arg($t);
                $_if( $is-etaReducible($func),
                    { $Some($AppT($Some2value(&self($func)), $arg)) },
                    { $_if( $is-etaReducible($arg),
                          { $Some($AppT($func, $Some2value(&self($arg)))) },
                          { $None }
                      )
                    }
                )
            } elsif convertTBool2P6Bool($is-LamT($t)) {
                my $var  = $LamT2var($t);
                my $body = $LamT2body($t);
                $_if( $is-etaRedex($t),
                    { $Some($AppT2func($body)) },
                    { $_if( $is-etaReducible($body),
                          { $Some($LamT($var, $Some2value(&self($body)))) },
                          { $None }
                      )
                    }
                )
            } else {
                die "fell off type-dispatch with type " ~ $t.WHAT.perl
            }
        }
    }
));