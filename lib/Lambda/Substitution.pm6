use v6;

use Lambda::Base;
use Lambda::BaseP6;
use Lambda::String;
use Lambda::Boolean;
use Lambda::MaybeADT;
use Lambda::TermADT;
use Lambda::FreeVars;
use Lambda::ListADT;
use Lambda::PairADT;


# Main reason for returning a Maybe (rather than eg the same Term if nothing changes)
# is that we don't need to compare terms for equality then.
constant $subst-seq is export = $Y(-> &self { lambdaFn(
    'subst-seq', 'λterm.λsubstitutions.error "NYI"',
    -> TTerm $t, TList $substitutions -->TMaybe{
        case-List($substitutions,
            nil  => $None,
            cons => -> TPair $head, TList:D $tail { case-Term($t,
                ConstT => $K1None,
                VarT => -> Str $tName {
                    my Str $forName = $fst($head);
                    _if_($Str-eq($forName, $tName),
                        {
                            my TTerm  $what = $snd($head);
                            my TMaybe $out  = &self($what, $tail);
                            case-Maybe($out,
                                None => { $Some($what) },
                                Some => -> Mu { $out }
                            )
                        },
                        { &self($t, $tail) }
                    )
                },

                AppT => -> TTerm $oldFunc, TTerm $oldArg {   # TODO
                    my $newFunc = &self($oldFunc, $substitutions);
                    my $newArg  = &self($oldArg,  $substitutions);
                    # iff applying &self retuns None for both, then nothing's changed and we return None
                    # otherwise return a Some AppT with .func/.arg replaced only if the resp. thing really changed (original otherwise)
                    case-Maybe($newFunc,
                        None => {
                            case-Maybe($newArg,
                                None => $None,
                                Some => -> TTerm $newArgVal{ $Some($AppT($oldFunc, $newArgVal)) }
                            )
                        },
                        Some => -> TTerm $newFuncVal {
                            $Some( $AppT(
                                $newFuncVal,
                                case-Maybe($newArg,
                                    None => $oldArg,
                                    Some => $I
                                )
                            ))
                        }
                    )

                },

                LamT => -> Str $tVarName, TTerm $tBody {   # DONE: LamT_ctor_with_Str_binder
                    my $newBody = &self(
                        $tBody,
                        $except( # kick out substitutions for our binder since there
                                 # won't be free occurrances of it in our body
                          -> $substPair { $Str-eq($tVarName, $fst($substPair)) },    #   $B($Str-eq($tVarName), $fst), # NOTE: fn composition via B is bad for perf...   #   
                          $substitutions
                        )
                    );
                    case-Maybe($newBody,
                        None => $None,
                        Some => -> TTerm $newBodyVal { $Some($LamT($tVarName, $newBodyVal)) }   # DONE: LamT_ctor_with_Str_binder
                    )
                }
            )}
        )
    }
)});



# Main reason for returning a Maybe (rather than eg the same Term if nothing changes)
# is that we don't need to compare terms for equality then.
constant $subst is export = lambdaFn(
    'subst', 'λfor.λwhat.λt.subst-seq t (cons (Pair for what) nil)',
    -> Str $forVarName, TTerm $what, TTerm $t -->TMaybe{
        $subst-seq($t, $cons($Pair($forVarName, $what), $nil));
    }
);


constant $subst-with-alpha is export = lambdaFn(
    'subst-with-alpha', 'λforVar.λwhatTerm.λkeepfree.λinTerm.error "NYI"',
    -> Str $forVarName, TTerm $whatTerm, TList $keepfreeNames, TTerm $inTerm {
        $Y(-> &self { lambdaFn(
            Str, 'λself.λalpha-convs.λt.error "NYI"',
            -> TList $alpha-convs, TTerm $t {
                case-Term($t,
                    ConstT => -> Mu { $Pair($None, $nil) },
                    VarT => -> Str $varName {
                        _if_($Str-eq($forVarName, $varName),
                            { $Pair($Some($whatTerm), $nil) },  # it's the main substitution (ie. no alpha-convs applicable)
                            { # otherwise (possibly an alpha-conv is applicable):
                                case-Maybe($first(-> $sPair { $Str-eq($varName, $fst($sPair)) }, $alpha-convs),
                                    None => { $Pair($None, $nil) }, # no alpha-conv applicable ~> nothing to change
                                    Some => -> $sPair {
                                        $Pair($Some($snd($sPair)), $cons($sPair, $nil))
                                    }
                                )
                            }
                        )
                    },
                    AppT => -> TTerm $func, TTerm $arg {
                        my $fp = &self($alpha-convs, $func);
                        my $f = $fst($fp);
                        my $ap = &self($alpha-convs, $arg);
                        my $a = $fst($ap);
                        case-Maybe($f,
                            None => {
                                case-Maybe($a,
                                    None => $Pair($None, $nil),
                                    Some => -> TTerm $newArg { $Pair($Some($AppT($func, $newArg)), $snd($ap)) }
                                )
                            },
                            Some => -> TTerm $newFunc {
                                case-Maybe($a,
                                    None => {
                                        $Pair(
                                            $Some($AppT($newFunc, $arg)),
                                            $snd($fp)
                                        )
                                    },
                                    Some => -> $newArg {
                                        my $fpConvs = $snd($fp);
                                        my $apConvs = $snd($ap);
                                        my $existsInApConvs = -> $p { 
                                            $exists(
                                                -> $q {
                                                    _if_($Str-eq($fst($p), $fst($q)), # short-circuit AND
                                                        { $Term-eq($snd($p), $snd($q)) },
                                                        $false
                                                    )
                                                },
                                                $apConvs) 
                                        };
                                        $Pair(
                                            $Some($AppT($newFunc, $newArg)),
                                            $append($except($existsInApConvs, $fpConvs), $apConvs)
                                        )
                                    }
                                )
                            }
                        )
                    },
                    LamT => -> Str $myVarName, TTerm $body {
                        my $newConvs  = $except(
                            -> TPair $s { $Str-eq($myVarName, $fst($s)) }, # (B (Str-eq? myVarName) fst)
                            $alpha-convs
                        );
                        _if_($Str-eq($myVarName, $forVarName),
                            # bound by the lambda, hence not free, so we only apply alpha-convs
                            {   case-Maybe($subst-seq($body, $newConvs),
                                    None => { $Pair($None, $nil) },
                                    Some => -> $newBody {
                                        $Pair(
                                            $Some($LamT($myVarName, $newBody)),
                                            $newConvs)
                                        }
                                )
                            },
                            {   my $needFreshVar = _if_(    # short-circuit AND
                                    $exists(
                                        -> Str $vName { $Str-eq($myVarName, $vName) },
                                        $keepfreeNames
                                    ),
                                    { $is-free-varName($forVarName, $body) },
                                    $false
                                );
                                _if_($needFreshVar,
                                    {   my $freshVar  = $fresh-var-for($VarT($myVarName));  # TODO: $fresh-var-for-name
                                        my $freshName = $VarT2name($freshVar);  # TODO: return Str from $fresh-name-for-name
                                        my $myAlpha  = $Pair($myVarName, $freshVar);
                                        my $p = &self($cons($myAlpha, $newConvs), $body);
                                        case-Maybe($fst($p),
                                            None => { $Pair($None, $nil) },  # neither forVar nor myVar free in body, and no external alpha-convs applicable
                                            Some => -> TTerm $newBody {
                                                $Pair(
                                                    $Some($LamT($freshName, $newBody)),
                                                    $snd($p)
                                                )
                                            }
                                        )
                                    },
                                    {   my $p = &self($newConvs, $body);
                                        case-Maybe($fst($p),
                                            None => { $Pair($None, $nil) },
                                            Some => -> TTerm $newBody {
                                                $Pair(
                                                    $Some($LamT($myVarName, $newBody)),
                                                    $snd($p)
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
        )})($nil, $inTerm);
    }
);

