use v6;

use Lambda::Base;
use Lambda::BaseP6;
use Lambda::Boolean;
use Lambda::String;
use Lambda::MaybeADT;
use Lambda::ListADT;
use Lambda::TermADT;
use Lambda::FreeVars;
use Lambda::Substitution;

use Lambda::Conversion::Bool-conv;


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
constant $betaContractXXX is export = $Y(-> &self { lambdaFn(
    'betaContract','λt.error "NYI"',
    -> TTerm $t -->TMaybe{
        case-Term($t,
            ConstT => $K1None,
            VarT => $K1None,
            LamT => -> Str $varName, TTerm $body {    # DONE: LamT_ctor_with_Str_binder
                _if_( $is-betaReducible($body),
                    { $Some($LamT($varName, $Some2value(&self($body)))) },    # DONE: LamT_ctor_with_Str_binder
                    $None
                )
            },
            AppT => -> TTerm $func, TTerm $arg {
                _if_( $is-betaReducible($t),
                    { _if_( $is-betaRedex($t),
                          {   my Str $funcVarName = $LamT2var($func);    # DONE: LamT_ctor_with_Str_binder
                              _if_( $is-Omega($t),
                                  { _if_( $Str-eq($funcVarName, $LamT2var($arg)),    # DONE: LamT_ctor_with_Str_binder
                                        $None, # func and arg are both the (literally) same omega
                                        { $Some($AppT($arg, $arg)) }  # otherwise one more step to make them so
                                  )},
                                  {   my TTerm $funcBody  = $LamT2body($func);
                                      my TList $alpha-problematic = $filter(
                                          # no need to filter out $var itself separately
                                          # since it cannot be free under itself in the body
                                          -> $binderName { $is-freeName-under($funcVarName, $binderName, $funcBody) },
                                          $free-varNames($arg)
                                      );
                                      case-List($alpha-problematic,
                                          nil  => {
                                              my $substituted-func = $subst($funcBody, $arg, $funcVarName);
                                              case-Maybe($substituted-func,   # TODO: use Maybe-or or something like that
                                                  None => { $Some($funcBody) },
                                                  Some => -> Mu { $substituted-func }
                                              )
                                          },
                                          cons => -> $head, TList:D $tail { die "NYI: alpha-convert for " ~ $List2Str($alpha-problematic) }
                                      )
                                  }
                              )
                          },
                          { _if_( $is-betaReducible($func),
                                { $Some($AppT($Some2value(&self($func)), $arg)) },
                                { $Some($AppT($func, $Some2value(&self($arg)))) }
                          )}
                    )},
                    $None
                )
            }
        )
    }
)});

my constant $liftedCtor2 = lambdaFn(
    Str, '',
    #$B($liftMaybe(&ctor($a1)), &transform2nd);
    
    #-> &ctor {
    #    my $liftedPartialCtor = $B($liftMaybe, &ctor);
    #    -> &transform2nd {
    #        $B($C($B, &transform2nd), $liftedPartialCtor );
    #    }
    #}
    
    #-> &ctor, &transform2nd {
    #    $B($C($B, &transform2nd), $B($liftMaybe, &ctor) );
    #}
    
    -> &ctor, &transform2nd {
        -> $a1, $a2 {
            case-Maybe(&transform2nd($a2),
                None => $None,
                Some => -> $a2transformed { $Some(&ctor($a1, $a2transformed)) }
            );
        }
    }
);


my constant $BBSomeAppT = lambdaFn(
    'BBSomeAppT', '(B Some) ° AppT',
    #-> $f, $a { $Some($AppT($f, $a)); }
    $B($B($Some), $AppT)
);

# betaContract: Term -> Maybe Term
# one-step β-simplification (either of $t or any (one) child)
constant $betaContract is export = $Y(-> &self {
    #my $LamT_intoMaybe = $liftedCtor2($LamT, &self) does name('LamT-into-Maybe');
    #my $AppT_intoMaybe = $liftedCtor2($AppT, &self) does name('AppT-into-Maybe');
    lambdaFn(
        'betaContract', 'λt.error "NYI"',
        -> TTerm $t { case-Term($t,
            VarT => $K1None,

            ConstT => $K1None,

            #LamT => -> Str $varName, TTerm $body {    # DONE: LamT_ctor_with_Str_binder
            #    $liftedCtor2($LamT, $varName, &self, $body)
            #},
            #LamT => $liftedCtor2($LamT, &self),
            #LamT => $LamT_intoMaybe,
            LamT => -> Str $varName, TTerm $body {    # DONE: LamT_ctor_with_Str_binder
                case-Maybe(&self($body),
                    None => $None,
                    Some => -> TTerm $newBody { $Some($LamT($varName, $newBody)) }    # DONE: LamT_ctor_with_Str_binder
                )
            },

            AppT => -> TTerm $func, TTerm $arg {
                my $K1AppT_func_contracted_arg = -> Mu {
                    #$AppT_intoMaybe($func, $arg)
                    case-Maybe(&self($arg),
                        None => $None,
                        Some => -> TTerm $newArg { $Some($AppT($func, $newArg)) }
                    )
                };
                case-Term($func,
                    #VarT => -> Mu { $liftedCtor2($AppT, $func, &self, $arg) },
                    #VarT => -> Mu { $B($liftMaybe($AppT($func)), &self)($arg) },
                    #VarT => -> Mu { $AppT_intoMaybe($func, $arg) },
                    VarT => $K1AppT_func_contracted_arg,
                    
                    #ConstT => -> Mu { $liftedCtor2($AppT, $func, &self, $arg) },
                    #ConstT => -> Mu { $AppT_intoMaybe($func, $arg) },
                    ConstT => $K1AppT_func_contracted_arg,
                    
                    # func is AppT
                    AppT => -> Mu, Mu {
                        #my $func2 = &self($func);
                        #$_if( $is-Some($func2),
                        #    -> Mu { $Some($AppT($Some2value($func2), $arg)) },
                        #    #-> Mu { $bindMaybe($func2, $B($Some, -> $func2val { $AppT($func2val, $arg) })) },
                        #    #-> Mu { $bindMaybe($func2, $B($Some, $C($AppT, $arg))) },
                        #    #-> Mu { $liftMaybe($C($AppT, $arg), $func2) },
                        #
                        #    #-> Mu { $liftedCtor2($AppT, $func, &self, $arg) }
                        #    -> Mu { $B($liftMaybe($AppT($func)), &self)($arg) }
                        #    -> Mu { $AppT_intoMaybe($func, $arg) }
                        #)
                        #case-Maybe(&self($func),
                            #None => $liftedCtor2($AppT, $func, &self),
                            #None => $B($liftMaybe($AppT($func)), &self),

                            #None => -> TTerm $arg { $AppT_intoMaybe($func, $arg) },
                            #None => $AppT_intoMaybe($func),
                        #    None => { $AppT_intoMaybe($func) },    # simulate lazy evaluation by passing a thunk (the block; needed only for ctors of arity 0)
                            
                            #Some => -> TTerm $reducedFunc {
                            #    -> TTerm $arg { $Some($AppT($reducedFunc, $arg)) }
                            #}
                            #Some => -> $reducedFunc { $B($Some, $AppT($reducedFunc)) }
                            #Some => $B($B($Some), $AppT)
                        #    Some => $BBSomeAppT
                        #)($arg);

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
                        my $alpha-problematic = $filter(
                            # no need to filter out $var itself separately
                            # since it cannot be free under itself in the body
                            -> Str $vName { $is-freeName-under($funcVarName, $vName, $funcBody) },
                            $free-varNames($arg)
                        );
                        case-List($alpha-problematic,
                            cons => -> Str $hd, TList $tl {
                                die 'NYI: alpha-convert for ' ~ $List2Str($alpha-problematic) ~ ' in β-redex ' ~ $Term2srcLess($t)
                            },
                            nil => {
                                my $substituted-func = $subst($funcBody, $arg, $funcVarName);
                                case-Maybe($substituted-func,
                                    None => { $Some($funcBody) },    # binder funcVarName did not occur in funcBody
                                    Some => -> Mu {
                                        # is t (literal) Omega? / pt 1: (omega? func)
                                        _if_( $is-selfAppOf($funcVarName, $funcBody),
                                            { my $K1substituted-func = $K($substituted-func);
                                              case-Term($arg,
                                                # is t (literal) Omega? / pt 2: (omega? arg)
                                                LamT => -> Str $argVarName, TTerm $argBody {    # DONE: LamT_ctor_with_Str_binder
                                                    _if_($Str-eq($funcVarName, $argVarName),  # short-circuit AND
                                                        { _if_($is-selfAppOf($argVarName, $argBody),
                                                              $None, # func and arg are both the (literally) same omega (same var used)
                                                              $substituted-func  # otherwise one more step to make them so
                                                        )},
                                                        $substituted-func
                                                    )
                                                },
                                                VarT => $K1substituted-func,
                                                AppT => -> Mu, Mu { $substituted-func },
                                                ConstT => $K1substituted-func
                                            )},
                                            $substituted-func
                                        )
                                    }
                                )
                            }
                        )
                    }
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
