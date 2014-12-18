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

constant $subst-first_VarT = lambdaFn(
    'subst-first_VarT',
q:to/ENDOFLAMBDA/,
    λname.λalpha-convs.error "NYI"
ENDOFLAMBDA
    -> Str $name, TList $alpha-convs {
        $Maybe-lift-in($B($Some, $snd))(
            $first(
                -> TPair $s { convertP6Bool2TBool($name eq $fst($s)) },
                $alpha-convs
            )
        )
    }
);

constant $subst-first = $Y(lambdaFn(
    'subst-first',
q:to/ENDOFLAMBDA/,
    λself.λt.λalpha-convs.error "NYI"
ENDOFLAMBDA
    -> &self {
        -> TTerm $t, TList $alpha-convs {
            if convertTBool2P6Bool($is-ConstT($t)) {
                $None
            } elsif convertTBool2P6Bool($is-VarT($t)) {
                $subst-first_VarT($VarT2name($t), $alpha-convs)
            } elsif convertTBool2P6Bool($is-AppT($t)) {
                my $func = $AppT2func($t);
                my $arg  = $AppT2arg($t);
                my $f = &self($func, $alpha-convs);
                my $a = &self($arg,  $alpha-convs);
                $_if( $is-None($f),
                    { $Maybe-lift-in(-> TTerm $newArg { $Some($AppT($func, $newArg)) })(  # (B Some (B (AppT func)))
                        $a
                      )
                      #$_if( $is-None($a),
                      #    { $None },
                      #    { $Some($AppT($func, $Some2value($a))) }
                      #)
                    },
                    { $Some($AppT(
                        $Some2value($f),
                        $Maybe2valueWithDefault($a, $arg)
                      ))
                      #$_if( $is-None($a),
                      #    { $Some($AppT($Some2value($f), $arg)) },
                      #    { $Some($AppT($Some2value($f), $Some2value($a))) }
                      #)
                    },
                )
            } elsif convertTBool2P6Bool($is-LamT($t)) {
                my $var   = $LamT2var($t);
                my $body  = $LamT2body($t);
                my $vName = $VarT2name($var);
                $Maybe-lift-in(-> $newBody { $LamT($var, $newBody) })(
                    &self($filter(-> TPair $s { $fst($s) ne $vName }, $alpha-convs), $body)
                )
            } else {
                die "fell off type-dispatch with type " ~ $t.WHAT.perl
            }
        }
    }
));

constant $subst-with-alpha is export = lambdaFn(
    'subst-with-alpha',
q:to/ENDOFLAMBDA/,
    λforVar.λwhatTerm.λkeepfree.λinTerm.error "NYI"
ENDOFLAMBDA
    -> TTerm $forVar, TTerm $whatTerm, TList $keepfree, TTerm $inTerm {
        my $forVarName    = $VarT2name($forVar);
        my $keepfreeNames = $map($VarT2name, $keepfree);
        my $mainSubst     = $Pair($forVarName, $whatTerm);
        $Y(lambdaFn(
            Str, 'λself.λalpha-convs.λt.error "NYI"',
            -> &self {
                -> TList $alpha-convs, TTerm $t {
                    if convertTBool2P6Bool($is-ConstT($t)) {
                        $None
                    } elsif convertTBool2P6Bool($is-VarT($t)) {
                        #$subst-first_VarT($VarT2name($t), $cons($mainSubst, $alpha-convs))
                        $_if( convertP6Bool2TBool($VarT2name($t) eq $forVarName),
                            { $Some($whatTerm) },
                            { $subst-seq($t, $alpha-convs) }
                        );
                    } elsif convertTBool2P6Bool($is-AppT($t)) {
                        my $func = $AppT2func($t);
                        my $arg  = $AppT2arg($t);
                        my $f = &self($alpha-convs, $func);
                        my $a = &self($alpha-convs, $arg);
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
                        my $myVar     = $LamT2var($t);
                        my $body      = $LamT2body($t);
                        my $myVarName = $VarT2name($myVar);
                        my $newConvs  = $filter(
                            -> $s { convertP6Bool2TBool($fst($s) ne $myVarName) }, # (not (B (eq? myVarName) fst))
                            $alpha-convs
                        );
                        $_if( convertP6Bool2TBool($forVarName eq $myVarName),
                            # bound by the lambda, hence not free, so we only apply alpha-convs
                            { $Maybe-lift-in(-> $newBody { $Some($LamT($myVar, $newBody)) })(
                                  $subst-first($body, $newConvs)
                              )

                              #$liftMaybe($LamT._($myVar))($subst-first($body, $newConvs))
                              ## (liftMaybe (LamT myVar) (subst-first body newConvs))

                              #my $newBody = $subst-seq($body, $newConvs);
                              #$_if( $is-None($newBody),
                              #    { $None },
                              #    { $Some($LamT($myVar, $Some2value($newBody))) }
                              #)
                            },
                            { my $needFreshVar = $exists(   # TODO: ... AND only if forVar occurs (free) in body
                                -> Str $vName {
                                    convertP6Bool2TBool($vName eq $myVarName)
                                },
                                $keepfreeNames
                              );
                              $_if($needFreshVar,
                                  { my $freshVar = $fresh-var-for($myVar);
                                    my $myConvs  = $cons($Pair($myVar, $freshVar), $newConvs);
                                    my $newBody  = &self($myConvs, $body);
                                    # if (is-None newBody) then neither forVar nor myVar free in body, and no external alpha-convs applicable
                                    $_if( $is-None($newBody),
                                        { $None },
                                        { $Some($LamT($freshVar, $Some2value($newBody))) }
                                    )
                                  },
                                  { my $newBody = &self($newConvs, $body);
                                    $_if( $is-None($newBody),
                                        { $None },
                                        { $Some($LamT($myVar, $Some2value($newBody))) }
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
        ))($nil, $inTerm);
    }
);