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


constant $except-substs_noDupes = $Y(-> &self { lambdaFn(
    'except-substs_noDupes', '',
    -> $skip, TList $xs {
        case-List($xs,
            nil => $nil,
            cons => -> $sPair, $rest {
                $sPair(-> $forName, $replacement {
                    my $newSkip = -> $vn {
                        _if_($Str-eq($forName, $vn),
                            $true,  # short-circuit OR
                            { $skip($vn) }
                        );
                    };
                    my $newRest = &self($newSkip, $rest);
                    _if_($skip($forName),
                        $newRest,
                        { $cons($sPair, $newRest) }
                    )
                })
            }
        )
    }
)});

constant $subst-par-alpha_direct is export = $Y(-> &self { lambdaFn(
    'subst-par-alpha_direct', 'λself.λsubstitutions.λt.error "NYI"',
    -> TList $substitutions, TTerm $t -->TTerm{
        case-Term($t,
            ConstT => -> Mu { $t },
            VarT => -> Str $varName {
                case-Maybe($first(-> $sPair { $Str-eq($varName, $fst($sPair)) }, $substitutions),
                    None => $t, # no alpha-conv applicable ~> nothing to change
                    Some => $snd
                )
            },
            AppT => -> TTerm $func, TTerm $arg {
                $AppT(
                    &self($substitutions, $func),
                    &self($substitutions, $arg)
                )
            },
            LamT => -> Str $binderName, TTerm $body {
                # kick out irrelevant substitutions:
                my $newSubsts = $except-substs_noDupes(
                    -> $forName {
                        _if_($Str-eq($binderName, $forName), # short-circuit OR
                            $true,
                            { $not($is-free-varName($forName, $body)) }
                        )
                    },
                    $substitutions
                );
                case-List($newSubsts,
                    nil => $t,
                    cons => -> Mu, Mu {
                        _if_($exists(-> $sPair { $is-free-varName($binderName, $snd($sPair)) }, $newSubsts),
                            {   my $freshVar  = $fresh-var-for($binderName);
                                my $freshName = $VarT2name($freshVar);  # TODO: return Str from $fresh-name-for-name
                                my $myAlpha  = $Pair($binderName, $freshVar);
                                $LamT($freshName, &self($cons($myAlpha, $newSubsts), $body));
                            },
                            { $LamT($binderName, &self($newSubsts, $body)) }
                        )
                    }
                )
            }
        )
    }
)});


constant $subst-par-alpha_Maybe is export = $Y(-> &self { lambdaFn(
    'subst-par-alpha_Maybe', 'λself.λsubstitutions.λt.error "NYI"',
    -> TList $substitutions, TTerm $t -->TMaybe{
        case-Term($t,
            ConstT => $K1None,
            VarT => -> Str $varName {
                case-Maybe($first(-> $sPair { $Str-eq($varName, $fst($sPair)) }, $substitutions),
                    None => $None, # no substitutions applicable ~> nothing to change
                    Some => -> $sPair { $Some($snd($sPair)) }   # Some ° snd
                )
            },
            AppT => -> TTerm $func, TTerm $arg {
                my $f = &self($substitutions, $func);
                my $a = &self($substitutions, $arg);
                case-Maybe($f,
                    None => {
                        case-Maybe($a,
                            None => $None,
                            Some => -> TTerm $newArg { $Some($AppT($func, $newArg)) }
                        )
                    },
                    Some => -> TTerm $newFunc {
                        case-Maybe($a,
                            None =>            { $Some($AppT($newFunc, $arg   )) },
                            Some => -> $newArg { $Some($AppT($newFunc, $newArg)) }
                        )
                    }
                )
            },
            LamT => -> Str $binderName, TTerm $body {
                # kick out irrelevant substitutions:
                my $newSubsts = $except-substs_noDupes(
                    -> $forName {
                        _if_($Str-eq($binderName, $forName), # short-circuit OR
                            $true,
                            { $not($is-free-varName($forName, $body)) }
                        )
                    },
                    $substitutions
                );
                case-List($newSubsts,
                    nil => $None,
                    cons => -> Mu, Mu {
                        _if_($exists(-> $sPair { $is-free-varName($binderName, $snd($sPair)) }, $newSubsts),
                            {   my $freshVar  = $fresh-var-for($binderName);
                                my $freshName = $VarT2name($freshVar);  # TODO: return Str from $fresh-name-for-name
                                my $myAlpha  = $Pair($binderName, $freshVar);
                                # Here we use the fact that we *know* that body will change:
                                $Some($LamT($freshName, $subst-par-alpha_direct($cons($myAlpha, $newSubsts), $body)));
                            },
                            { case-Maybe(&self($newSubsts, $body),
                                  None => $None,
                                  Some => -> TTerm $newBody { $Some($LamT($binderName, $newBody)) }
                            ) }
                        )
                    }
                )
            }
        )
    }
)});


constant $subst-par-alpha is export = $subst-par-alpha_Maybe but name('subst-par-alpha');
#constant $subst-par-alpha is export = $subst-par-alpha_direct but name('subst-par-alpha');


# specialized variant of subst-par-alpha_direct: if there's exactly one substitution
constant $subst-alpha_direct is export = $Y(-> &self { lambdaFn(
    'subst-alpha_direct', 'λself.λforName.λreplacement.λinTerm.error "NYI"',
    -> Str $forName, TTerm $replacement, TTerm $inTerm -->TTerm{
        case-Term($inTerm,
            ConstT => -> Mu { $inTerm },
            VarT => -> Str $varName {
                _if_($Str-eq($forName, $varName),
                    $replacement,
                    $inTerm
                )
            },
            AppT => -> TTerm $func, TTerm $arg {
                my $f = &self($forName, $replacement, $func);
                my $a = &self($forName, $replacement, $arg);
                $AppT($f, $a);
            },
            LamT => -> Str $myVarName, TTerm $body {
                _if_($Str-eq($forName, $myVarName), # do we bind the substitution var?
                    $inTerm,  # ...if so, nothing to do
                    {_if_($is-free-varName($forName, $body),    # is substitution var occuring in our body, after all?
                        {_if_($is-free-varName($myVarName, $replacement),   # need alpha-conv?
                            {   my $freshVar  = $fresh-var-for($myVarName);
                                my $freshName = $VarT2name($freshVar);  # TODO: return Str from $fresh-name-for-name
                                my $mainSubst = $Pair($forName, $replacement);
                                my $myAlpha   = $Pair($myVarName, $freshVar);
                                my $substitutions = $cons($myAlpha, $cons($mainSubst, $nil));
                                
                                $LamT($freshName, $subst-par-alpha_direct($substitutions, $body));
                            },
                            { $LamT($myVarName, &self($forName, $replacement, $body)) }
                        )},
                        $inTerm   # substitution var not occuring in body ~> nothing to do
                    )}
                )
            }
        )
    }
)});


# specialized variant of subst-par-alpha_Maybe: if there's exactly one substitution
constant $subst-alpha_Maybe is export = $Y(-> &self { lambdaFn(
    'subst-alpha_Maybe', 'λself.λforName.λreplacement.λinTerm.error "NYI"',
    -> Str $forName, TTerm $replacement, TTerm $inTerm -->TMaybe{
        case-Term($inTerm,
            ConstT => $K1None,
            VarT => -> Str $varName {
                _if_($Str-eq($forName, $varName),
                    { $Some($replacement) },
                    $None
                )
            },
            AppT => -> TTerm $func, TTerm $arg {
                my $f = &self($forName, $replacement, $func);
                my $a = &self($forName, $replacement, $arg);
                case-Maybe($f,
                    None => {
                        case-Maybe($a,
                            None => $None,
                            Some => -> TTerm $newArg { $Some($AppT($func, $newArg)) }
                        )
                    },
                    Some => -> TTerm $newFunc {
                        case-Maybe($a,
                            None =>            { $Some($AppT($newFunc, $arg   )) },
                            Some => -> $newArg { $Some($AppT($newFunc, $newArg)) }
                        )
                    }
                )
            },
            LamT => -> Str $myVarName, TTerm $body {
                _if_($Str-eq($forName, $myVarName), # do we bind the substitution var?
                    $None,  # ...if so, nothing to do
                    {_if_($is-free-varName($forName, $body),    # is substitution var occuring in our body, after all?
                        {_if_($is-free-varName($myVarName, $replacement),   # need alpha-conv?
                            {   my $freshVar  = $fresh-var-for($myVarName);
                                my $freshName = $VarT2name($freshVar);  # TODO: return Str from $fresh-name-for-name
                                my $mainSubst = $Pair($forName, $replacement);
                                my $myAlpha   = $Pair($myVarName, $freshVar);
                                my $substitutions = $cons($myAlpha, $cons($mainSubst, $nil));
                                
                                $Some($LamT($freshName, $subst-par-alpha_direct($substitutions, $body)));
                            },
                            # TODO: use the fact that we *know* that body will change
                            { $Some($LamT($myVarName, $subst-alpha_direct($forName, $replacement, $body))) }
                        )},
                        $None   # substitution var not occuring in body ~> nothing to do
                    )}
                )
            }
        )
    }
)});
