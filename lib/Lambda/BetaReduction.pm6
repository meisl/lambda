use v6;

use Lambda::Base;
use Lambda::BaseP6;
use Lambda::Boolean;
use Lambda::String;
use Lambda::MaybeADT;
use Lambda::ListADT;
use Lambda::PairADT;
use Lambda::TermADT;
use Lambda::FreeVars;
use Lambda::Substitution;

use Lambda::Conversion;


# β-redex?: Term -> Bool
# is it a Term of form ((λx.B) z)?
constant $is-betaRedex is export = lambdaFn(
    'betaRedex?', 'λt.error "NYI"',
    -> TTerm:D $t -->TBool{
        case-Term($t,
            VarT   => $K1false,
            ConstT => $K1false,
            LamT   => $K2false,
            AppT   => -> TTerm $func, TTerm $arg {
                # (P Q) is a β-redex if P is of form (λx.B).
                # If so, it β-contracts to [P/x] B, ie P substituted for x
                # in the λ's body but beware: any free var in P
                # must NOT be accidentally captured by a binding in B.
                # If that would be the case, we need to α-convert before.
                $is-LamT($func)
            }
        )
    }
);


# betaReducible?: Term -> Bool
# either t is a β-redex or any child is betaReducible?
constant $is-betaReducible is export = $Y(-> &self { lambdaFn(
    'betaReducible?', 'λt.error "NYI"',
    -> TTerm $t -->TBool{
        _if_( $is-betaRedex($t),       # short-circuit OR
            $true,
            { $exists(&self, $Term2children($t)) }
        )
    }
)});


# alpha-problematic-varNames: Term -> List Str
constant $alpha-problematic-varNames is export = lambdaFn(
    'alpha-problematic-varNames', 'λt.error "NYI"',
    -> TTerm $t -->TList{
        case-Term($t,
            ConstT => $K1nil,
            VarT => $K1nil,
            LamT => $K2nil,
            AppT => -> TTerm $func, TTerm $arg {
                case-Term($func,
                    ConstT => $K1nil,
                    VarT => $K1nil,
                    AppT => $K2nil,
                    LamT => -> Str $varName, TTerm $body {  # DONE: LamT_ctor_with_Str_binder
                        # func is a LamT, so t is a beta-redex...
                        $filter(
                            -> $binderName {
                              # no need to filter out $var itself separately
                              # since it cannot be free under itself in the body
                              $is-freeName-under($varName, $binderName, $body)
                            },
                            $free-varNames($arg)
                        )
                    }
                )
            }
        )
    }
);

# alpha-problematic-var: Term -> List Term
constant $alpha-problematic-vars is export = lambdaFn(
    'alpha-problematic-vars', 'λt.error "NYI"',
    -> TTerm $t -->TList{ $map($VarT, $alpha-problematic-varNames($t)) }
);

# alpha-problematic-varNames: Term -> List Term
constant $alpha-needy-terms is export = $Y(-> &self { lambdaFn(
    'alpha-needy-terms', 'λt.λkeepfreevars.error "NYI"',
    -> TTerm $t, TList $keepfreevars -->TList{
        case-Term($t,
            ConstT => $K1nil,
            VarT => $K1nil,
            AppT => -> TTerm $func, TTerm $arg {
                $append(&self($func, $keepfreevars), &self($arg, $keepfreevars));
            },
            LamT => -> Str $varName, TTerm $body {  # DONE: LamT_ctor_with_Str_binder
                my $fromBody = &self($body, $keepfreevars);
                _if_( $exists( -> $v { $Str-eq($varName, $VarT2name($v)) }, $keepfreevars),
                    { $cons($t, $fromBody) },
                    { $fromBody },
                );
            }
        );
    }
)});



# betaContract: Term -> Maybe Term
# one-step β-simplification (either of $t or any (one) child)
constant $betaContract is export = $Y(-> &self {
    lambdaFn(
        'betaContract', 'λt.error "NYI"',
        -> TTerm $t { case-Term($t,
            VarT   => $K1None,
            ConstT => $K1None,
            LamT   => -> Str $varName, TTerm $body {    # DONE: LamT_ctor_with_Str_binder
                case-Maybe(&self($body),
                    None => $None,
                    Some => -> TTerm $newBody { $Some($LamT($varName, $newBody)) }    # DONE: LamT_ctor_with_Str_binder
                )
            },
            AppT => -> TTerm $func, TTerm $arg {
                my $K1AppT_func_contracted_arg = -> Mu {
                    case-Maybe(&self($arg),
                        None => $None,
                        Some => -> TTerm $newArg { $Some($AppT($func, $newArg)) }
                    )
                };
                case-Term($func,
                    VarT   => $K1AppT_func_contracted_arg,
                    ConstT => $K1AppT_func_contracted_arg,
                    AppT   => -> Mu, Mu {
                        case-Maybe(&self($func),
                            None => {    # simulate lazy evaluation by passing a thunk (the block; needed only for ctors of arity 0)
                                #$AppT_intoMaybe($func, $arg)
                                case-Maybe(&self($arg),
                                    None => $None,
                                    Some => -> TTerm $newArg { $Some($AppT($func, $newArg)) }
                                )
                            },
                            Some => -> TTerm $newFunc { $Some($AppT($newFunc, $arg)) }
                        );
                    },
                    
                    LamT => -> Str $funcVarName, TTerm $funcBody {    # DONE: LamT_ctor_with_Str_binder
                    # so t is a beta-redex
                        my $newFuncBody-M = $subst-alpha_Maybe($funcVarName, $arg, $funcBody);
                        case-Maybe($newFuncBody-M,
                            None => { $Some($funcBody) },   # Note: t cannot be Omega if subst didn't change anything
                            Some => -> $newFuncBody {
                                # Here we have to check if t is (literal) Omega:
                                _if_( $is-selfAppOf($funcVarName, $funcBody),   # pt 1: (omega? func)   / short-circuit AND
                                    { _if_($is-omegaOf($funcVarName, $arg),     # pt 2: is arg (literally) the same omega as func?
                                        $None, # ...if so then t is Omega and nothing really changes
                                        $newFuncBody-M
                                    )},
                                    $newFuncBody-M
                                )
                            }
                        )
                    },
                )
            }
        )}
    )
});


# betaReduce: Term -> Maybe Term
# β-contract until fixed-point (Ω is considered a fixed-point, too)
# Main reason for returning a Maybe (rather than eg the same Term if nothing changes)
# is that we don't need to compare terms for equality then.
constant $betaReduce is export = lambdaFn(
    'betaReduce', 'findFP-inMaybe betaContract',
    $findFP-inMaybe($betaContract)
);


# Given (at least) one `arg`, and a LamT (determined by `binderName` and `body`):
# descend further any chain of LamT s as long as there are rest-args, while
# turning them into appropriate substitution pairs.
# Stop and apply substitutions (in parallel) if either there are no more `rest-args`
# or the term is non-LamT.
# Then call `finalize` with the result of this parallel substitution and a list of the
# still-unapplied rest args.
constant $apply-args is export = $Y(-> &self { lambdaFn(
    'apply-args', # : (Term -> [Term]-> a) -> [<Str, Term>] -> Term -> [Term] -> Str -> Term -> a
    'λfinalize.λsubstitutions.λarg.λrest-args.λbinderName.λbody.error "NYI"',
    -> $finalize, TList $substitutions, $arg, TList $rest-args, Str $binderName, TTerm $body {
        case-Term($body,
            LamT => -> $bodyVarName, $bodyBody {
                case-List($rest-args,
                    nil => {    # ran out of args - none left for body (which is also a LamT)
                        my $newBody = _if_($Str-eq($bodyVarName, $binderName),    # does body (also a lambda) mask our own binder?
                            { $subst-par-alpha_direct(                                $substitutions,  $body) },
                            { $subst-par-alpha_direct($cons($Pair($binderName, $arg), $substitutions), $body) }
                        );
                        $finalize($newBody, $nil);
                    },
                    cons => -> $a, $as {
                        my $newSubsts = $cons($Pair($binderName, $arg), $substitutions);
                        &self($finalize, $newSubsts, $a, $as, $bodyVarName, $bodyBody);
                    }
                );
                
            },
            ConstT => -> Mu { $finalize($body, $rest-args) },
            VarT   => -> $bodyVarName {
                _if_($Str-eq($binderName, $bodyVarName),
                    { $finalize($arg, $rest-args) },
                    { $finalize(case-Maybe($first(-> $sPair { $Str-eq($bodyVarName, $fst($sPair)) }, $substitutions),
                                None => $body,
                                Some => $snd    # return value of Some as is
                            ),
                            $rest-args
                    ) }
                )
            },
            AppT   => -> Mu, Mu {
                $finalize(
                    $subst-par-alpha_direct($cons($Pair($binderName, $arg), $substitutions), $body), 
                    $rest-args
                )
            },
        )
    }
)});


# Descend chains of AppT, collecting arguments to be applied once a LamT is encountered.
# If indeed a LamT is encountered in an AppT's func position, onLambda is called with the
# LamT's binder (name), the LamT's body, the last arg encountered so far and a list of 
# all the args above (in bottom-up order, ie in the order they're to be fed to the LamT).
# Otherwise onUnapplicable is called with the unapplicable term, the last arg encountered
# so far and a list of all the args above; again in bottom-up order.
# Both callbacks, onUnapplicable and onLambda must return a TMaybe, which is taken to mean this:
# - a Some indicates a final result, and is returned from collect-args as is (no further call to
#   any of the two callbacks)
# - a None indicates that the callback did not change the term at hand, given it plus the current
#   arg and the rest-args (at the current level in the chain of AppTs).
#   onUnapplicable will be called with the term and arg(s) one level up, or, respectively, if the
#   call-stack has been unwound completely, the None will be returned from collect-args.
constant $collect-args is export = $Y(-> &self { lambdaFn(
    'collect-args', # : (Term -> [Term]-> a) -> (Str -> Term -> [Term]-> a) -> [Term] -> Term -> a
    'λonUnapplicable.λonLambda.λarg.λrest-args.λinTerm.error "NYI"',
    -> $onUnapplicable, $onLambda, TTerm $arg, TList $rest-args, TTerm $inTerm {
        case-Term($inTerm,
            ConstT => -> Mu { $onUnapplicable($inTerm, $arg, $rest-args) },
            VarT   => -> Mu { $onUnapplicable($inTerm, $arg, $rest-args) },
            AppT   => -> $f, $a {
                my $newRest-args = $cons($arg, $rest-args);
                my $newFm = &self($onUnapplicable, $onLambda, $a, $newRest-args, $f);
                case-Maybe($newFm,
                    None => { $onUnapplicable($inTerm, $arg, $rest-args) },  # (onUnapplicable f a newRest-args) already done in recursive call
                    Some => -> Mu { $newFm }
                )
            },
            LamT   => -> $v, $b { $onLambda($v, $b, $arg, $rest-args) }
        )
    }
)});

constant $collect-lambdas = $Y(-> &self { lambdaFn(
    'collect-lambdas', 'λss.λv.λb.λa.λas.error "NYI"', 
    -> $onInsideLambda, TList $bindings, TTerm $body, TList $rest-args {
        case-Term($body,
            LamT => -> Str $bv, TTerm $bb {
                case-List($rest-args,
                    cons => -> TTerm $a, TList $as {
                        my $newBindings = $cons($Pair($bv, $a), $bindings);
                        &self($onInsideLambda, $newBindings, $bb, $as)
                    },
                    nil => {    # ran out of args - none left for body (which is also a LamT)
                        $onInsideLambda($bindings, $body, $nil)
                    }
                )
            },
            AppT   => -> Mu, Mu { $onInsideLambda($bindings, $body, $rest-args) },
            VarT   => -> Mu     { $onInsideLambda($bindings, $body, $rest-args) },
            ConstT => -> Mu     { $onInsideLambda($bindings, $body, $rest-args) },
        );
    }
)});

constant $collect-args-and-lambdas is export = {
    lambdaFn(
        'collect-args-and-lambdas', # : (Term -> [Term]-> a) -> (Str -> Term -> [Term]-> a) -> [Term] -> Term -> a
        'λonUnapplicable.λonInsideLambda.λarg.λrest-args.λinTerm.error "NYI"',
        -> $onUnapplicable, $onInsideLambda, TTerm $arg, TList $rest-args, TTerm $inTerm {
            $collect-args(
                $onUnapplicable,
                -> $v, $b, $arg, $rest-args {
                    my $bindings = $cons($Pair($v, $arg), $nil);
                    $Some($collect-lambdas($onInsideLambda, $bindings, $b, $rest-args))
                },
                $arg, $rest-args, $inTerm
            );
        }
    );
}();

# betaContract_multi: Term -> Maybe Term
# β-simplification (either of $t or any (one) child), reducing AppT s of multiple args in one step if possible
constant $betaContract_multi is export = $Y(-> &self { 
    my $onUnapplicable = -> TTerm $func, TTerm $arg, TList $rest-args {
        case-Maybe(&self($arg),
            None => $None,
            Some => -> $newArg { $Some($foldl($AppT, $AppT($func, $newArg), $rest-args)) }
        );
    };

    my $onLamT = -> Str $binderName, TTerm $body, TTerm $arg, TList $rest-args {
        $Some($apply-args(
            $foldl($AppT),  # "finalize"
            $nil,           # "substitutions"
            $arg, $rest-args,
            $binderName, $body
        ));
    };

    my $filter-substs-and-contract = $Y(-> &self2 { lambdaFn(
        'filter-substs-and-contract', '',
        -> $skip, TList $substs {
            case-List($substs,
                nil => $nil,
                cons => -> $sPair, $rest {
                    $sPair(-> $forName, $replacement {
                        my $newSkip = -> $vn {
                            _if_($Str-eq($forName, $vn),  # short-circuit OR
                                $true,
                                { $skip($vn) }
                            );
                        };
                        my $newRest = &self2($newSkip, $rest);
                        _if_($skip($forName),
                            $newRest,
                            { $cons(case-Maybe(&self($replacement),
                                        None => $sPair,
                                        Some => -> $newArg { $Pair($forName, $newArg) },
                                    ),
                                    $newRest
                            ) }
                        )
                    })
                }
            )
        }
    )});

    my $doSubsts = lambdaFn('doSubsts', '', -> TList $bindings, TTerm $inTerm {
        my $newBindings = $filter-substs-and-contract(
            -> Str $forName { $is-not-free-varName($forName, $inTerm) },
            $bindings
        );
        $subst-par-alpha_direct($newBindings, $inTerm);
    });

    my $doSubsts-lambda = lambdaFn('doSubsts-lambda', '', -> TList $bindings, Str $binderName, TTerm $body {
        my $newBindings = $filter-substs-and-contract(
            -> Str $forName {
                _if_($Str-eq($binderName, $forName),   # short-circuit OR
                    $true,
                    { $is-not-free-varName($forName, $body) }
                )
            },
            $bindings
        );
        _if_($exists(-> $sPair { $is-free-varName($binderName, $snd($sPair)) }, $newBindings),
            {   # need fresh binder for binder
                my $freshVar = $fresh-var-for($binderName);
                $LamT($VarT2name($freshVar), $subst-par-alpha_direct($cons($Pair($binderName, $freshVar), $newBindings), $body));
            },
            { $LamT($binderName, $subst-par-alpha_direct($newBindings, $body)) }
        );
    });

    my $doSubsts-var = lambdaFn('doSubsts-var', '', -> TList $bindings, TTerm $varTerm, TList $rest-args, Str $varName {
        case-Maybe($first(-> $sPair { $Str-eq($varName, $fst($sPair)) }, $bindings),
            None => { $foldl($AppT, $varTerm, $rest-args) },
            Some => -> TPair $sPair {
                my $arg = $snd($sPair);
                case-Maybe(&self($arg), # could use _direct variant of &self
                    None => { $foldl($AppT, $arg, $rest-args) },
                    Some => -> TTerm $contractedArg {
                        $foldl($AppT, $contractedArg, $rest-args)
                    }
                )
            }
        )
    });

    my $onInsideLambda = $Y(-> &onInsideLambda { lambdaFn(Str, 'onInsideLambda', -> TList $bindings, TTerm $body, TList $rest-args {
        #my $newBody = $subst-par-alpha_direct($bindings, $body);
        #$foldl($AppT, $newBody, $rest-args);
        
        case-Term($body,
            VarT   => -> $bodyVarName { $doSubsts-var($bindings, $body, $rest-args, $bodyVarName) },
            ConstT => -> Mu { $foldl($AppT, $body, $rest-args) },
            AppT   => -> Mu, Mu {
                case-Maybe(&self($body),
                    None => {   # still an AppT, so we cannot apply more of rest-args
                        my $substitutedBody = $doSubsts($bindings, $body);
                        $foldl($AppT, $substitutedBody, $rest-args);
                    },
                    Some => -> $contractedBody {
                        case-List($rest-args,
                            nil => {
                                $doSubsts($bindings, $contractedBody);
                            },
                            cons => -> TTerm $arg, TList $more-args {
                                case-Term($contractedBody,
                                    ConstT => -> Mu {   # nothing to substitute (in)
                                        $foldl($AppT, $contractedBody, $rest-args)
                                    },
                                    VarT => -> $varName { # we can avoid subst-par-alpha, and do the (simple) substitution right here
                                        $doSubsts-var($bindings, $contractedBody, $rest-args, $varName)
                                    },
                                    AppT => -> Mu, Mu {
                                        $foldl($AppT, $doSubsts($bindings, $contractedBody), $rest-args)
                                    },
                                    LamT => -> $cbv, $cbb {
                                        $collect-lambdas(&onInsideLambda, $cons($Pair($cbv, $arg), $bindings), $cbb, $more-args)
                                    },
                                );
                            }
                        )
                    }
                );
                
                #$substitutedBody = case-Maybe(&self($substitutedBody), None => $substitutedBody, Some => $I);
                
            },
            LamT   => -> Str $bv, TTerm $bb {
                #my $contractedBody = case-Maybe(&self($body), # could use _direct variant of &self
                #    None => $body,
                #    Some => $I
                #);
                #my $substitutedBody = $doSubsts($bindings, $contractedBody);
                ##$substitutedBody = case-Maybe(&self($substitutedBody), None => $substitutedBody, Some => $I);
                #$substitutedBody;

                my $substitutedBody = case-Maybe(&self($bb),
                    None => { $doSubsts-lambda($bindings, $bv, $bb) },
                    Some => -> $contractedBb {
                        $doSubsts-lambda($bindings, $bv, $contractedBb);
                    }
                );

                #$substitutedBody = case-Maybe(&self($substitutedBody), None => $substitutedBody, Some => $I); # could use _direct variant of &self
                $substitutedBody;
                # Note: we *know* there cannot be any rest-args, so no need to foldl 'em up in the end
            },
        );
    })});
    
    lambdaFn(
        'betaContract_multi', 'λt.error "NYI"',
        -> TTerm $t { case-Term($t,
            VarT   => $K1None,
            ConstT => $K1None,
            LamT   => -> Str $varName, TTerm $body {
                case-Maybe(&self($body),
                    None => $None,
                    Some => -> TTerm $newBody { $Some($LamT($varName, $newBody)) }
                )
            },
            AppT   => -> TTerm $f, TTerm $a {

#                $collect-args($onUnapplicable, $onLamT, $a, $nil, $f);

                $collect-args-and-lambdas($onUnapplicable, $onInsideLambda, $a, $nil, $f);

                #case-Term($f,
                #    ConstT => -> Mu {
                #        case-Maybe(&self($a),
                #            None => $None,
                #            Some => -> $newA { $Some($AppT($f, $newA)) }
                #        )
                #    },
                #    VarT => -> Mu {
                #        case-Maybe(&self($a),
                #            None => $None,
                #            Some => -> $newA { $Some($AppT($f, $newA)) }
                #        )
                #    },
                #    LamT => -> $fv, $fb {
                #        $Some($subst-alpha_direct($fv, $a, $fb))
                #    },
                #    AppT => -> $ff, $fa {
                #        # $collect-then-apply-args(
                #        #    -> $t, $rest-args { # onNoneApplied
                #        #        
                #        #    },
                #        #    -> $t, $rest-args { # onSomeApplied
                #        #        $Some($foldl($AppT, $t, $rest-args))
                #        #    },
                #        #    $fa, $cons($a, $nil), $ff
                #        #);
                #        case-Maybe($collect-args($fa, $cons($a, $nil), $ff),
                #            None => {
                #                case-Maybe(&self($fa),   # TODO: try beta-contracting ff (but consider that it's got no LamT "on the left")
                #                    None => {
                #                        case-Maybe(&self($a),
                #                            None => $None,
                #                            Some => -> $newA {
                #                                $Some($AppT($f, $newA))
                #                            }
                #                        )
                #                    },
                #                    Some => -> $newFa {
                #                        $Some($AppT($AppT($ff, $newFa), $a))
                #                    }
                #                )
                #            },
                #            Some => -> TPair $p {
                #                my $t = $fst($p);   # TODO: extract fields from Pair directly
                #                my $rest-args = $snd($p);
                #                $Some($foldl($AppT, $t, $rest-args));
                #            }
                #        )
                #    }
                #)


            }
        )}
    )
});

