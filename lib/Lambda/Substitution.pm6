use v6;

use Lambda::Base;
use Lambda::BaseP6;
use Lambda::Boolean;
use Lambda::MaybeADT;
use Lambda::TermADT;
use Lambda::ListADT;
use Lambda::PairADT;

use Lambda::Conversion::Bool-conv;



# Main reason for returning a Maybe (rather than eg the same Term if nothing changes)
# is that we don't need to compare terms for equality then.
constant $subst-seq is export = $Y(-> &self { lambdaFn(
    'subst-seq', 'λterm.λsubstitutions.error "NYI"',
    -> TTerm $t, TList $ss -->TMaybe{
        case-List($ss,
            nil  => $None,
            cons => -> $head, TList:D $tail { case-Term($t,
                ConstT => $K1None,
                VarT   => -> $tName {   # TODO
                    my $for  = $fst($head);
                    my $what = $snd($head);
                    $_if( convertP6Bool2TBool($VarT2name($for) eq $VarT2name($t)),
                        -> $_ { my $out = &self($what, $tail);
                             $_if( $is-Some($out),
                                 -> $_ { $out },
                                 -> $_ { $Some($what) }
                             )
                        },
                        -> $_ { &self($t, $tail) }
                    )
                },
                AppT   => -> $oldFunc, $oldArg {   # TODO
                    my $newFunc = &self($oldFunc, $ss);
                    my $newArg  = &self($oldArg,  $ss);
                    $_if( $_and($is-None($newFunc), $is-None($newArg)),
                        -> $_ { $None },
                        -> $_ { $Some( $AppT(
                             $_if( $is-Some($newFunc), -> $_ { $Some2value($newFunc) }, -> $_ { $oldFunc } ),
                             $_if( $is-Some($newArg),  -> $_ { $Some2value($newArg)  }, -> $_ { $oldArg  } )
                          ))
                        }
                    )
                },
                LamT   => -> $tVar, $tBody {   # TODO
                    my $body = &self(
                        $tBody,
                        $filter( # kick out substs for our binder since there
                                 # won't be free occurrances of it in our body
                          -> $x { convertP6Bool2TBool($VarT2name($fst($x)) ne $VarT2name($tVar)) },
                          $ss
                        )
                    );
                    $_if( $is-None($body),
                        -> $_ { $None },
                        -> $_ { $Some($LamT($tVar, $Some2value($body))) }
                    )
                }
            )}
        )
    }
)});



# Main reason for returning a Maybe (rather than eg the same Term if nothing changes)
# is that we don't need to compare terms for equality then.
constant $subst is export = lambdaFn(
    'subst', 'λt.λwhat.λfor.subst-seq t (cons (Pair for what) nil)',
    -> TTerm $t, TTerm $what, TTerm $for -->TTerm{    # TODO: add types to signature
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

constant $subst-first = $Y(-> &self { lambdaFn(
    'subst-first',
q:to/ENDOFLAMBDA/,
    λself.λt.λalpha-convs.error "NYI"
ENDOFLAMBDA
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
                -> $_ { $Maybe-lift-in(-> TTerm $newArg { $Some($AppT($func, $newArg)) })(  # (B Some (B (AppT func)))
                          $a
                        )
                        #$_if( $is-None($a),
                        #    -> $_ { $None },
                        #    -> $_ { $Some($AppT($func, $Some2value($a))) }
                        #)
                },
                -> $_ { $Some($AppT(
                            $Some2value($f),
                            $Maybe2valueWithDefault($a, $arg)
                        ))
                        #$_if( $is-None($a),
                        #    -> $_ { $Some($AppT($Some2value($f), $arg)) },
                        #    -> $_ { $Some($AppT($Some2value($f), $Some2value($a))) }
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
)});

constant $subst-with-alpha is export = lambdaFn(
    'subst-with-alpha',
q:to/ENDOFLAMBDA/,
    λforVar.λwhatTerm.λkeepfree.λinTerm.error "NYI"
ENDOFLAMBDA
    -> TTerm $forVar, TTerm $whatTerm, TList $keepfree, TTerm $inTerm {
        my $forVarName    = $VarT2name($forVar);
        my $keepfreeNames = $map($VarT2name, $keepfree);
        my $mainSubst     = $Pair($forVarName, $whatTerm);
        $Y(-> &self { lambdaFn(
            Str, 'λself.λalpha-convs.λt.error "NYI"',
            -> TList $alpha-convs, TTerm $t {
                if convertTBool2P6Bool($is-ConstT($t)) {
                    $None
                } elsif convertTBool2P6Bool($is-VarT($t)) {
                    #$subst-first_VarT($VarT2name($t), $cons($mainSubst, $alpha-convs))
                    $_if( convertP6Bool2TBool($VarT2name($t) eq $forVarName),
                        -> $_ { $Some($whatTerm) },
                        -> $_ { $subst-seq($t, $alpha-convs) }
                    );
                } elsif convertTBool2P6Bool($is-AppT($t)) {
                    my $func = $AppT2func($t);
                    my $arg  = $AppT2arg($t);
                    my $f = &self($alpha-convs, $func);
                    my $a = &self($alpha-convs, $arg);
                    $_if( $is-None($f),
                        -> $_ { $_if( $is-None($a),
                                    -> $_ { $None },
                                    -> $_ { $Some($AppT($func, $Some2value($a))) }
                                )
                        },
                        -> $_ { $_if( $is-None($a),
                                    -> $_ { $Some($AppT($Some2value($f), $arg)) },
                                    -> $_ { $Some($AppT($Some2value($f), $Some2value($a))) }
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
                        -> $_ { $Maybe-lift-in(-> $newBody { $Some($LamT($myVar, $newBody)) })(
                                    $subst-first($body, $newConvs)
                                )

                                #$liftMaybe($LamT._($myVar))($subst-first($body, $newConvs))
                                ## (liftMaybe (LamT myVar) (subst-first body newConvs))

                                #my $newBody = $subst-seq($body, $newConvs);
                                #$_if( $is-None($newBody),
                                #    -> $_ { $None },
                                #    -> $_ { $Some($LamT($myVar, $Some2value($newBody))) }
                                #)
                        },
                        -> $_ { my $needFreshVar = $exists(   # TODO: ... AND only if forVar occurs (free) in body
                                    -> Str $vName {
                                        convertP6Bool2TBool($vName eq $myVarName)
                                    },
                                    $keepfreeNames
                                );
                                $_if( $needFreshVar,
                                    -> $_ { my $freshVar = $fresh-var-for($myVar);
                                            my $myConvs  = $cons($Pair($myVar, $freshVar), $newConvs);
                                            my $newBody  = &self($myConvs, $body);
                                            # if (is-None newBody) then neither forVar nor myVar free in body, and no external alpha-convs applicable
                                            $_if( $is-None($newBody),
                                                -> $_ { $None },
                                                -> $_ { $Some($LamT($freshVar, $Some2value($newBody))) }
                                            )
                                    },
                                    -> $_ { my $newBody = &self($newConvs, $body);
                                            $_if( $is-None($newBody),
                                                -> $_ { $None },
                                                -> $_ { $Some($LamT($myVar, $Some2value($newBody))) }
                                            )
                                    }
                                );
                        }
                    );
                } else {
                    die "fell off type-dispatch with type " ~ $t.WHAT.perl
                }
            }
        )})($nil, $inTerm);
    }
);