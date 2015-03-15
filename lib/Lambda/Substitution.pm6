use v6;

use Lambda::Base;
use Lambda::BaseP6;
use Lambda::String;
use Lambda::Boolean;
use Lambda::MaybeADT;
use Lambda::TermADT;
use Lambda::ListADT;
use Lambda::PairADT;


# Main reason for returning a Maybe (rather than eg the same Term if nothing changes)
# is that we don't need to compare terms for equality then.
constant $subst-seq is export = $Y(-> &self { lambdaFn(
    'subst-seq', 'λterm.λsubstitutions.error "NYI"',
    -> TTerm $t, TList $substitutions -->TMaybe{
        case-List($substitutions,
            nil  => $None,
            cons => -> $head, TList:D $tail { case-Term($t,
                ConstT => $K1None,
                VarT   => -> $tName {
                    my $forName = $VarT2name($fst($head));
                    _if_($Str-eq($forName, $tName),
                        {
                            my $what = $snd($head);
                            my $out  = &self($what, $tail);
                            case-Maybe($out,
                                None => { $Some($what) },
                                Some => -> Mu { $out }
                            )
                        },
                        { &self($t, $tail) }
                    )
                },

                AppT   => -> $oldFunc, $oldArg {   # TODO
                    my $newFunc = &self($oldFunc, $substitutions);
                    my $newArg  = &self($oldArg,  $substitutions);
                    # iff both are None then nothing's changed and we return None
                    # otherwise return a Some AppT with .func/.arg replaced only if the resp. thing really changed (original otherwise)
                    case-Maybe($newFunc,
                        None => {
                            case-Maybe($newArg,
                                Some => -> $newArgVal{
                                    $Some($AppT($oldFunc, $newArgVal))
                                },
                                None => $None
                            )
                        },
                        Some => -> $newFuncVal {
                            $Some( $AppT(
                                $newFuncVal,
                                case-Maybe($newArg,
                                    Some => $pi1o1,
                                    None => $oldArg
                                )
                            ))
                        }
                    )

                },

                LamT   => -> $tVar, $tBody {
                    my $body = &self(
                        $tBody,
                        $except( # kick out substitutions for our binder since there
                                 # won't be free occurrances of it in our body
                          -> $substPair { $Term-eq($tVar, $fst($substPair)) },    #   $B($Term-eq($tVar), $fst), # NOTE: fn composition via B is bad for perf...   #   
                          $substitutions
                        )
                    );
                    case-Maybe($body,
                        None => $None,
                        Some => -> $bodyVal { $Some($LamT($tVar, $bodyVal)) }
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
                -> TPair $s { $Str-eq($name, $fst($s)) },
                $alpha-convs
            )
        )
    }
);

constant $subst-first = $Y(-> &self { lambdaFn(
    'subst-first', 'λself.λterm.λalpha-convs.error "NYI"',
    -> TTerm $t, TList $alpha-convs {
        case-Term($t,
            ConstT => $K1None,
            VarT   => -> Str $name { $subst-first_VarT($name, $alpha-convs) },
            AppT   => -> TTerm $func, TTerm $arg {
                my $f = &self($func, $alpha-convs);
                my $a = &self($arg,  $alpha-convs);
                case-Maybe($f,
                    None => {
                        $Maybe-lift-in(-> TTerm $newArg { $Some($AppT($func, $newArg)) })(  # (B Some (B (AppT func)))
                            $a
                        )
                        #case-Maybe($a,
                        #    None => $None,
                        #    Some => -> $newArg { $Some($AppT($func, $newArg)) }
                        #)
                    },
                    Some => -> $newFunc {
                        $Some($AppT(
                            $newFunc,
                            $Maybe2valueWithDefault($a, $arg)
                            #case-Maybe($a,
                            #    None => $arg,
                            #    Some => $I
                            #)
                        ))

                        #case-Maybe($a,
                        #    None => { $Some($AppT($newFunc), $arg)) },
                        #    Some => -> $newArg { $Some($AppT($newFunc), $newArg)) }
                        #)
                    }
                )
            },
            LamT   => -> TTerm $var, TTerm $body {
                my $varName = $VarT2name($var);
                $Maybe-lift-in(-> $newBody { $LamT($var, $newBody) })(
                    &self($body, $except(-> TPair $s { $Str-eq($varName, $fst($s)) }, $alpha-convs))         # <<<<<<<<<<<<<<<<<<<<< !?
                )
            }
        )
    }
)});

constant $subst-with-alpha is export = lambdaFn(
    'subst-with-alpha', 'λforVar.λwhatTerm.λkeepfree.λinTerm.error "NYI"',
    -> TTerm $forVar, TTerm $whatTerm, TList $keepfree, TTerm $inTerm {
        my $forVarName    = $VarT2name($forVar);
        my $keepfreeNames = $map($VarT2name, $keepfree);
        my $mainSubst     = $Pair($forVarName, $whatTerm);
        $Y(-> &self { lambdaFn(
            Str, 'λself.λalpha-convs.λt.error "NYI"',
            -> TList $alpha-convs, TTerm $t {
                case-Term($t,
                    ConstT => $K1None,
                    VarT   => -> Str $varName {
                        #$subst-first_VarT($varName, $cons($mainSubst, $alpha-convs))
                        $_if( $Str-eq($forVarName, $varName),
                            -> $_ { $Some($whatTerm) },
                            -> $_ { $subst-seq($t, $alpha-convs) }
                        );
                    },
                    AppT   => -> TTerm $func, TTerm $arg {
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
                    },
                    LamT   => -> TTerm $myVar, TTerm $body {
                        my $myVarName = $VarT2name($myVar);
                        my $newConvs  = $except(
                            -> $s { $Str-eq($myVarName, $fst($s)) }, # (B (eq? myVarName) fst)
                            $alpha-convs
                        );
                        $_if( $Str-eq($forVarName, $myVarName),
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
                                        -> Str $vName { $Str-eq($myVarName, $vName) },
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
                    }
                )
            }
        )})($nil, $inTerm);
    }
);

