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


# apply-args: List (Pair Str Term) -> List Term -> Pair (Maybe Term) (List Term)
# Descend chains of LamT s as long as there are rest-args, while
# turning them into appropriate substitution pairs.
# Stop and apply substitutions if either there are no more rest-args
# or the term is non-LamT.
# Return a Pair in which the fst (Maybe Term) indicates whether term has changed
# and the snd contains the still unapplied rest-args.
# Note: when called with non-empty list of rest-args on a LamT *always* returns a Some.
constant $apply-args is export = $Y(-> &self { lambdaFn(
    'apply-args', 'λsubstitutions.λrest-args.λterm.error "NYI"',
    -> TList $substitutions, TList $rest-args, TTerm $t -->TPair{
        case-Term($t,
            ConstT => -> Mu   { $Pair($None, $rest-args) },
            VarT => -> Mu     { $Pair($subst-par-alpha($substitutions, $t), $rest-args) },
            AppT => -> Mu, Mu { $Pair($subst-par-alpha($substitutions, $t), $rest-args) },
            LamT => -> $vName, $body {
                case-List($rest-args,
                    nil => { $Pair($subst-par-alpha($substitutions, $t), $rest-args) },
                    cons => -> $a, $as {
                        my $out = &self($cons($Pair($vName, $a), $substitutions), $as, $body);
                        case-Maybe($fst($out),
                            None => { $Pair($Some($body), $snd($out)) },
                            Some => -> Mu { $out }
                        )
                    }
                )
            }
        )
    }
)});

# Variant of apply-args specialized for the LamT case *where we have a non-empty list of rest-args*
constant $apply-args_direct is export = $Y(-> &self { lambdaFn(
    'apply-args_direct', 'λsubstitutions.λrest-args.λbinderName.λbody.error "NYI"',
    -> TList $substitutions, $arg, TList $rest-args, Str $binderName, TTerm $body -->TPair{
        case-Term($body,
            LamT => -> $bodyVarName, $bodyBody {
                case-List($rest-args,
                    nil => {    # ran out of args - none left for body (which is also a LamT)
                        my $newSubsts = $except(
                            -> $sPair { $Str-eq($bodyVarName, $fst($sPair)) }, 
                            $substitutions
                        );
                        _if_($Str-eq($bodyVarName, $binderName),
                            { $Pair($subst-par-alpha_direct(                                $newSubsts,  $bodyBody), $nil) },
                            { $Pair($subst-par-alpha_direct($cons($Pair($binderName, $arg), $newSubsts), $bodyBody), $nil) }
                        )
                    },
                    cons => -> $a, $as {
                        my $newSubsts = $cons($Pair($binderName, $arg), $substitutions);
                        &self($newSubsts, $a, $as, $bodyVarName, $bodyBody);
                    }
                );
                
            },
            ConstT => -> Mu { $Pair($body, $rest-args) },
            VarT   => -> $bodyVarName {
                _if_($Str-eq($binderName, $bodyVarName),
                    { $Pair($arg, $rest-args) },
                    { $Pair(case-Maybe($first(-> $sPair { $Str-eq($bodyVarName, $fst($sPair)) }, $substitutions),
                                None => $body,
                                Some => $snd    # return value of Some as is
                            ),
                            $rest-args
                    ) }
                )
            },
            AppT   => -> Mu, Mu {
                $Pair(
                    $subst-par-alpha_direct($cons($Pair($binderName, $arg), $substitutions), $body), 
                    $rest-args
                )
            },
        )
    }
)});

