use v6;

use Lambda::Base;
use Lambda::Boolean;
use Lambda::MaybeADT;
use Lambda::TermADT;
use Lambda::ListADT;
use Lambda::PairADT;

use Lambda::Conversion::Bool-conv;


constant $subst-seq is export = $Y(lambdaFn(
    'subst-seq',
q:to/ENDOFLAMBDA/,
    λself.λt.λss.
      (if (nil? ss)
          None
          (if (VarT? t)
              (let ((head (car ss))
                    (next (if (eq? (VarT->name (fst head)) (VarT->name t))  ; FIXME!
                              (snd head)
                              t)))
                (self next (cdr ss))
              )
              (if (AppT? t)
                  (let ((f (AppT->func t))
                        (a (AppT->arg  t))
                        (f´ (self f ss))
                        (a´ (self a ss))
                       )
                    (if (and (None? f') (None? a'))
                      None
                      (Some (AppT
                              (if (Some? f´) (Some->value f´) f)
                              (if (Some? a´) (Some->value a´) a)
                      ))
                    )
                  )
                  (if (LamT? t)
                      (let ((var (LamT->var t))
                            (nm  (VarT->name var))
                            (ss´ (filter    ; kick out substs for our binder
                                   (λv.not (eq? (VarT->name v) nm))
                                   ss))
                            (b´  (self (VarT->body t) ss´))
                           )
                        (if (Some? b´)
                            (Some (LamT var (Some->value b´)))
                            None
                        )
                      )
                      # TODO: ConstT -> None
                      (error (~ "unknown Term ctor: " (Term->Str t)))
                  )
              )
          )
      )
ENDOFLAMBDA
    -> &self {
        -> TTerm $t, TList $ss {
            $_if( $is-nil($ss),
                { $None },
                { $_if( $is-ConstT($t),
                      { $None },
                      { $_if( $is-VarT($t),
                            { my $head = $car($ss);
                              my $for  = $fst($head);
                              my $what = $snd($head);
                              my $tail = $cdr($ss);
                              $_if( convertP6Bool2TBool($VarT2name($for) eq $VarT2name($t)),
                                  { my $out = &self($what, $tail);
                                    $_if( $is-Some($out),
                                        { $out },
                                        { $Some($what) }
                                    )
                                  },
                                 { &self($t, $tail) }
                              )
                            },
                            { $_if( $is-AppT($t),
                                  { my $oldFunc = $AppT2func($t);
                                    my $oldArg  = $AppT2arg($t);
                                    my $newFunc = &self($oldFunc, $ss);
                                    my $newArg  = &self($oldArg,  $ss);
                                    $_if( $_and($is-None($newFunc), $is-None($newArg)),
                                        { $None },
                                        { $Some( $AppT(
                                                   $_if( $is-Some($newFunc), { $Some2value($newFunc) }, { $oldFunc } ),
                                                   $_if( $is-Some($newArg),  { $Some2value($newArg)  }, { $oldArg  } )
                                          ))
                                        }
                                    )
                                  },
                                  { $_if( $is-LamT($t),
                                        { my $body = &self(
                                              $t.body,
                                              $filter( # kick out substs for our binder since there
                                                       # won't be free occurrances of it in our body
                                                -> $x { convertP6Bool2TBool($VarT2name($fst($x)) ne $VarT2name($LamT2var($t))) },
                                                $ss
                                              )
                                          );
                                          $_if( $is-Some($body),
                                              { $Some($LamT($LamT2var($t), $Some2value($body))) },
                                              { $None }
                                          )
                                        },
                                        { die "fell off type-dispatch with type " ~ $t.WHAT.perl }
                                    )
                                  }
                              )
                            }
                        )
                      }
                  )
                }
            )
        }
    }
));

constant $subst is export = lambdaFn(
    'subst', 'λt.λwhat.λfor.subst-seq t (cons (Pair for what) nil)',
    -> TTerm $t, TTerm $what, TTerm $for {    # TODO: add types to signature
        $subst-seq($t, $cons($Pair($for, $what), $nil));
    }
);
