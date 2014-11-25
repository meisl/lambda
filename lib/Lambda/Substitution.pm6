use v6;

use Lambda::Base;
use Lambda::Boolean;
use Lambda::MaybeADT;
use Lambda::TermADT;
use Lambda::ListADT;
use Lambda::PairADT;

use Lambda::Conversion::Bool-conv;



# Main reason for returning a Maybe (rather than eg the same Term if nothing changes)
# is that we don't need to compare terms for equality then.
constant $subst-seq is export = $Y(lambdaFn(
    'subst-seq',
q:to/ENDOFLAMBDA/,
    λself.λt.λss.
      (if (nil? ss)
          None
          (if (VarT? t) ; TODO: case ConstT
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
                    (if (and (None? f´) (None? a´))
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
                            (b´  (self (LamT->body t) ss´))
                           )
                        (if (None? b´)
                            None
                            (Some (LamT var (Some->value b´)))
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
                                              $LamT2body($t),
                                              $filter( # kick out substs for our binder since there
                                                       # won't be free occurrances of it in our body
                                                -> $x { convertP6Bool2TBool($VarT2name($fst($x)) ne $VarT2name($LamT2var($t))) },
                                                $ss
                                              )
                                          );
                                          $_if( $is-None($body),
                                              { $None },
                                              { $Some($LamT($LamT2var($t), $Some2value($body))) }
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



# Main reason for returning a Maybe (rather than eg the same Term if nothing changes)
# is that we don't need to compare terms for equality then.
constant $subst is export = lambdaFn(
    'subst', 'λt.λwhat.λfor.subst-seq t (cons (Pair for what) nil)',
    -> TTerm $t, TTerm $what, TTerm $for {    # TODO: add types to signature
        $subst-seq($t, $cons($Pair($for, $what), $nil));
    }
);

constant $subst-with-alpha is export = $Y(lambdaFn(
    'subst-with-alpha',
q:to/ENDOFLAMBDA/,
    λself.λforVar.λwhatTerm.λkeepfree.λalpha-convs.λt.error "NYI"
ENDOFLAMBDA
    -> &self {
        -> TTerm $forVar, TTerm $whatTerm, TList $keepfree, TList $alpha-convs, TTerm $t {
            if convertTBool2P6Bool($is-ConstT($t)) {
                $None
            } elsif convertTBool2P6Bool($is-VarT($t)) {
                $_if( convertP6Bool2TBool($VarT2name($t) eq $VarT2name($forVar)),
                    { $Some($whatTerm) },
                    { $subst-seq($t, $alpha-convs) }
                );
            } elsif convertTBool2P6Bool($is-AppT($t)) {
                my $func = $AppT2func($t);
                my $arg  = $AppT2arg($t);
                my $f = &self($forVar, $whatTerm, $keepfree, $alpha-convs, $func);
                my $a = &self($forVar, $whatTerm, $keepfree, $alpha-convs, $arg);
                $_if( $is-None($f),
                    { $_if( $is-None($a),
                          { $None },
                          { $Some($AppT($func, $Some2value($a))) }
                      )
                    },
                    { $_if( $is-None($a),
                          { $Some($AppT($Some2value($f), $arg)) },
                          { $Some($AppT($Some2value($f), $Some2value($a))) }
                      )
                    },
                )
            } elsif convertTBool2P6Bool($is-LamT($t)) {
                my $var       = $LamT2var($t);
                my $body      = $LamT2body($t);
                my $myVarName = $VarT2name($var);
                my $newConvs  = $filter(
                    -> $conv { convertP6Bool2TBool($VarT2name($fst($conv)) ne $myVarName) }, # (not (B (B (eq? myVarName) VarT->name) fst))
                    $alpha-convs
                );
                $_if( convertP6Bool2TBool($VarT2name($forVar) eq $myVarName),
                    { my $newBody = $subst-seq($body, $newConvs); # if we bind it then it's not free -> apply only alpha-convs
                      $_if( $is-None($newBody),
                          { $None },
                          { $Some($LamT($var, $Some2value($newBody))) }
                      )
                    },
                    { my $needFreshVar = $exists(   # TODO: ... AND only if forVar occurs (free) in body
                        -> TTerm $v {
                            convertP6Bool2TBool($VarT2name($v) eq $myVarName)
                        },
                        $keepfree
                      );
                      $_if($needFreshVar,
                          { my $freshVar = $fresh-var-for($var);
                            my $myConvs  = $cons($Pair($var, $freshVar), $newConvs);
                            my $newBody  = &self($forVar, $whatTerm, $keepfree, $myConvs, $body);
                            $_if( $is-None($newBody), # neither forVar nor var free in body, and no external alpha-convs applicable
                                { $None },
                                { $Some($LamT($freshVar, $Some2value($newBody))) }
                            )
                          },
                          { my $newBody = &self($forVar, $whatTerm, $keepfree, $newConvs, $body);
                            $_if( $is-None($newBody),
                                { $None },
                                { $Some($LamT($var, $Some2value($newBody))) }
                            )
                          }
                      );
                    }
                );
            } else {
                die "fell off type-dispatch with type " ~ $t.WHAT.perl
            }
        }
    }
));