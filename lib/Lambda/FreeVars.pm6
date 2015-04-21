use v6;

use Lambda::Base;
use Lambda::BaseP6;
use Lambda::Boolean;
use Lambda::String;
use Lambda::MaybeADT;
use Lambda::ListADT;
use Lambda::TermADT;


constant $is-free-varName is export = $Y(-> &self { lambdaFn(
    'free-varName?', 'λself.λvarName.λt.error "NYI"',
    -> Str:D $varName, TTerm $t -->TBool{
        case-Term($t,
            ConstT => $K1false,
            VarT => -> Str $name { $Str-eq($varName, $name) },
            AppT => -> TTerm $func, TTerm $arg {
                _if_( &self($varName, $func),       # short-circuit OR
                    $true,
                    { &self($varName, $arg) }
                )
            },
            LamT => -> Str $binderName, TTerm $body {
                _if_( $Str-ne($varName, $binderName),   # short-circuit AND
                    { &self($varName, $body) },
                    $false,
                )
            }
        );
    }
)});


constant $is-not-free-varName is export = $Y(-> &self { lambdaFn(
    'not-free-varName?', 'λself.λvarName.λt.error "NYI"',
    -> Str:D $varName, TTerm $t -->TBool{
        case-Term($t,
            ConstT => $K1true,
            VarT => -> Str $name { $Str-ne($varName, $name) },
            AppT => -> TTerm $func, TTerm $arg {
                _if_( &self($varName, $func),       # short-circuit AND
                    { &self($varName, $arg) },
                    $false
                )
            },
            LamT => -> Str $binderName, TTerm $body {
                _if_( $Str-eq($varName, $binderName),   # short-circuit OR
                    $true,
                    { &self($varName, $body) }
                )
            }
        );
    }
)});

constant $is-free is export = lambdaFn(
    'free?', 'B free-varName? VarT->name',
    $B($is-free-varName, $VarT2name)
);


constant $is-freeName-under is export = $Y(-> &self { lambdaFn(
    'freeName-under?', 'λself.λvarName.λbinderName.λt.error "NYI"',
    -> Str $varName, Str $binderName, TTerm $t -->TBool{
        case-Term($t,
            ConstT => $K1false,
            VarT => $K1false,
            AppT => -> TTerm $func, TTerm $arg {
                _if_(&self($varName, $binderName, $func),  # short-circuit OR
                    $true,
                    { &self($varName, $binderName, $arg) }
                )
            },
            LamT => -> Str $lamVarName, TTerm $body {    # DONE: LamT_ctor_with_Str_binder
                _if_($Str-ne($varName, $lamVarName),    # short-circuit AND
                    {   _if_( $Str-eq($binderName, $lamVarName),        # or else, if the binder is the λ's var then...
                            { $is-free-varName($varName, $body) },      # $var is free under $binder if $var is free in the λ's body
                            { &self($varName, $binderName, $body) }     # otherwise it depends on the λ's body
                        )
                    },
                    $false, # if the λ binds the var then it's not free anywhere in the λ's body
                );
            }
        )
    }
)});


constant $is-free-under is export = lambdaFn(
    'free-under?', 'λvar.λbinder.is-freeName? (VarT->name var) (VarT->name binder)',
    -> TTerm $var, TTerm $binder, TTerm $t { $is-freeName-under($VarT2name($var), $VarT2name($binder), $t) }
);

constant $free-var is export = $Y(-> &self { lambdaFn(
    'free-var', 'λname.λterm.error "NYI"',
    -> Str:D $name, TTerm $t -->TMaybe{
        case-Term($t,
            ConstT => $K1None,
            VarT => -> Str $thisName {
                _if_( $Str-eq($name, $thisName),
                    { $Some($t) },
                    $None
                )
            },
            AppT => -> TTerm $func, TTerm $arg {
                my $fromFunc = &self($name, $func);
                case-Maybe($fromFunc,
                    None => { &self($name, $arg) },    # simulate lazy evaluation by passing a thunk (the block; needed only for ctors of arity 0)
                    Some => -> Mu { $fromFunc }
                )
            },
            LamT => -> Str $varName, TTerm $body {    # DONE: LamT_ctor_with_Str_binder
                _if_( $Str-eq($name, $varName),
                    $None,
                    { &self($name, $body) }
                )
            }
        )
    }
)});


constant $free-varNames-internal = $Y(-> &self { lambdaFn(
    'free-varNames-internal', 'λbindersAbove.λresults.λterm.error "NYI"',
    -> TList:D $bindersAbove, TList:D $results, TTerm:D $t -->TList{
        my $K1results = -> Mu { $results };
        case-Term($t,
            ConstT => $K1results,   # t is a ConstT ~> leave results as is
            VarT => -> Str $varName {
                #my $eqVarName = $Str-eq($varName);
                _if_( $exists(-> Str $bName { $Str-eq($varName, $bName) }, $bindersAbove),
                    $results,     # don't add bound variable (ie leave results as is)
                    {
                        _if_( $exists(-> Str $rName { $Str-eq($varName, $rName) }, $results),
                            $results,     # don't make duplicates (ie leave results as is)
                            { $cons($varName, $results) }
                        )
                    }
                )
            },
            AppT => -> TTerm $func, TTerm $arg {
                my $freeInArg = &self($bindersAbove, $results, $arg);
                &self($bindersAbove, $freeInArg, $func);
            },
            LamT => -> Str $varName, TTerm $body {        # DONE: LamT_ctor_with_Str_binder
                &self($cons($varName, $bindersAbove), $results, $body);
            }
        )
    }
)});

constant $free-varNames is export = lambdaFn('free-varNames', 'free-varNames-internal nil nil', $free-varNames-internal($nil, $nil));


constant $free-vars-internal = $Y(-> &self { lambdaFn(
    'free-vars-internal', 'λbindersAbove.λresults.λterm.error "NYI"',
    -> TList $bindersAbove, TList $results, TTerm $t -->TList{
        my $K1results = -> Mu { $results };
        case-Term($t,
            ConstT => $K1results,   # t is a ConstT ~> leave results as is
            VarT => -> Str $varName {
                my $eqVar = -> TTerm $var {
                    $Str-eq($varName, $VarT2name($var))
                };
                _if_( $exists($eqVar, $bindersAbove),
                    $results,     # don't add bound variable (ie leave results as is)
                    {
                        _if_( $exists($eqVar, $results),
                            $results,     # don't make duplicates (ie leave results as is)
                            { $cons($t, $results) }
                        )
                    }
                )
            },
            AppT => -> TTerm $func, TTerm $arg {
                my $freeInArg = &self($bindersAbove, $results, $arg);
                &self($bindersAbove, $freeInArg, $func);
            },
            LamT => -> Str $varName, TTerm $body {    # DONE: LamT_ctor_with_Str_binder
                &self($cons($VarT($varName), $bindersAbove), $results, $body);
            }
        )
    }
)});

#constant $free-vars is export = lambdaFn('free-vars', 'free-vars-internal nil nil', $free-vars-internal($nil, $nil));
constant $free-vars is export = lambdaFn('free-vars', 'λterm.map VarT (free-varNames term)', -> TTerm $term { $map($VarT, $free-varNames($term)) });
