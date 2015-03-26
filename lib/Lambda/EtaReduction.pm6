use v6;

use Lambda::Base;
use Lambda::BaseP6;
use Lambda::Boolean;
use Lambda::String;
use Lambda::MaybeADT;
use Lambda::ListADT;
use Lambda::TermADT;
use Lambda::FreeVars;

use Lambda::Conversion;


# η-redex? - ie of form λx.(B x) where x not free in B
constant $is-etaRedex is export = lambdaFn(
    'etaRedex?', 'λt.error "NYI"',
    -> TTerm:D $t {
        #match-Term($t,
        #    '(LamT vName (AppT bf (VarT vName))' => -> $vName, $bf {
        #        $not($is-free-varName($vName, $bf))
        #    },
        #    otherwise => $false
        #)
        case-Term($t,
            ConstT => $K1false,
            VarT => $K1false,
            AppT => $K2false,
            LamT => -> Str $varName, TTerm $body {   # DONE: LamT_ctor_with_Str_binder
                # λx.(B x) is an η-redex if x not free in B.
                # (if so, it η-contracts to just B)
                case-Term($body,
                    ConstT => $K1false,
                    VarT => $K1false,
                    LamT => $K2false,
                    AppT => -> TTerm $func, TTerm $arg {
                        case-Term($arg,
                            ConstT => $K1false,
                            LamT => $K2false,
                            AppT => $K2false,
                            VarT => -> Str $argName {   # DONE: LamT_ctor_with_Str_binder
                                _if_( $Str-eq($argName, $varName),   # short-circuit AND
                                    { $not($is-free-varName($varName, $func)) },
                                    $false
                                )
                            }
                        )
                    }
                )
            }
        )
    }
);


# either t is an η-redex or any child is etaReducible?
constant $is-etaReducible is export = $Y(-> &self { lambdaFn(
    'etaReducible?', 'λt.error "NYI"',
    -> TTerm $t {
        _if_( $is-etaRedex($t), # short-circuit OR
            $true,
            { $exists(&self, $Term2children($t)) }
        )
    }
)});


# etaContract: one-step η-simplification, either of η-redex itself or any (one) child

# Main reason for returning a Maybe (rather than eg the same Term if nothing changes)
# is that we don't need to compare terms for equality then.
constant $etaContract is export = $Y(-> &self { lambdaFn(
    'etaContract', 'λt.error "NYI"',
    -> TTerm $t {
        case-Term($t,
            ConstT => $K1None,
            VarT => $K1None,
            AppT => -> TTerm $func, TTerm $arg {
                _if_( $is-etaReducible($func),
                    { $Some($AppT($Some2value(&self($func)), $arg)) },
                    { _if_( $is-etaReducible($arg),
                        { $Some($AppT($func, $Some2value(&self($arg)))) },
                        $None
                    )}
                )
            },
            LamT => -> Str $varName, TTerm $body {    # DONE: LamT_ctor_with_Str_binder
                _if_( $is-etaRedex($t),
                    { $Some($AppT2func($body)) },
                    { _if_( $is-etaReducible($body),
                          { $Some($LamT($varName, $Some2value(&self($body)))) },    # DONE: LamT_ctor_with_Str_binder
                          $None
                    )}
                )
            }
        )
    }
)});


# etaReduce: η-contract until fixed-point

# Main reason for returning a Maybe (rather than eg the same Term if nothing changes)
# is that we don't need to compare terms for equality then.
constant $etaReduce is export = $findFP-inMaybe($etaContract) does Definition('etaReduce');
