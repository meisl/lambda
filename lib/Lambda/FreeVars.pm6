use v6;

use Lambda::Base;
use Lambda::BaseP6;
use Lambda::Boolean;
use Lambda::String;
use Lambda::MaybeADT;
use Lambda::ListADT;
use Lambda::TermADT;

use Lambda::Conversion::Bool-conv;


constant $is-free-varName is export = $Y(-> &self { lambdaFn(
    'free-varName?', 'λself.λeq-varName?.λt.error "NYI"',
    -> $equalsVarName, TTerm $t -->TBool{
        case-Term($t,
            ConstT => $K1false,
            VarT   => $equalsVarName,
            AppT   => -> TTerm $func, TTerm $arg {
                _if_( &self($equalsVarName, $func),       # short-circuit OR
                    $true,
                    { &self($equalsVarName, $arg) }
                )
            },
            LamT   => -> TTerm $lamVar, TTerm $body {
                _if_( $equalsVarName($VarT2name($lamVar)),
                    $false,
                    { &self($equalsVarName, $body) }
                )
            }
        );
    }
)});

constant $is-free is export = lambdaFn(
    'free?', 'λvar.free-varName (Str-eq? (VarT->name var))',  # free-varName (B Str-eq? VarT->name)
    -> TTerm $var {
        $is-free-varName($Str-eq($VarT2name($var)));
    }
);

constant $is-free-under is export = $Y(-> &self { lambdaFn(
    'free-under?', 'λself.λvar.λbinder.λt.error "NYI"',
    -> TTerm $var, TTerm $binder, TTerm $t -->TBool{
        case-Term($t,
            VarT   => $K1false,
            ConstT => $K1false,
            AppT   => -> TTerm $func, $arg {
                _if_(&self($var, $binder, $func),  # short-circuit OR
                    $true,
                    { &self($var, $binder, $arg) }
                )
            },
            LamT   => -> TTerm $lamVar, $body {
                my $lamVarName = $VarT2name($lamVar);
                my $equalsLamVarName = -> Str $name {
                    convertP6Bool2TBool($lamVarName eq $name)
                };
                my $vName    = $VarT2name($var);
                _if_($equalsLamVarName($vName),
                    $false,               # if the λ binds the var then it's not free anywhere in the λ's body
                    {   my $bName = $VarT2name($binder);
                        _if_( $equalsLamVarName($bName),     # or else, if the binder is the λ's var then...
                            { $is-free($var, $body) },       # $var is free under $binder if $var is free in the λ's body
                            { &self($var, $binder, $body) }  # otherwise it depends on the λ's body
                        )
                    },
                );
            }
        );
    }
)});


constant $free-var is export = $Y(-> &self { lambdaFn(
    'free-var', 
 q:to/ENDOFLAMBDA/,
    λself.λname.λt.
        (case t
            (((ConstT val)    None)
             ((VarT tName)    (_if (eq? name tName)
                                (λ_.Some t)
                                (λ_.None)
                              )
             )
             ((AppT func arg) (let ((fromFunc (self name func))
                                    (inFunc?  (Some? fromFunc))
                                   )
                                (_if inFunc?
                                  fromFunc
                                  (self name arg)
                                )
                              )
             
             )
             ((LamT v body)   (_if (eq? name (VarT->name v))
                                (λ_.None)
                                (λ_.self name body)
                              )
             )
             (error (~ "unknown TTerm" (Term->Str t)))
           )
        )
ENDOFLAMBDA
    -> Str:D $name, TTerm $t {
        case-Term($t,
            ConstT   => $K1None,
            VarT     => -> Str $thisName {
                $_if( convertP6Bool2TBool($name eq $thisName),
                    -> Mu { $Some($t) },
                    $K1None
                )
            },
            AppT => -> TTerm $func, TTerm $arg {
                my $fromFunc = &self($name, $func);
                case-Maybe($fromFunc,
                    None => { &self($name, $arg) },    # simulate lazy evaluation by passing a thunk (the block; needed only for ctors of arity 0)
                    Some => -> Mu { $fromFunc }
                )
            },
            LamT => -> TTerm $var, TTerm $body {
                $_if( convertP6Bool2TBool($name eq $VarT2name($var)),
                    $K1None,
                    -> Mu { &self($name, $body) }
                )
            }
        )
    }
)});


constant $___free-vars is export = $Y(-> &self { lambdaFn(
    'free-vars', 
 q:to/ENDOFLAMBDA/,
    λself.λt.
        (case t
            (((ConstT val)    nil)
             ((VarT name)     (cons t nil)
             )
             ((AppT func arg) (let ((argFVs      (self arg))
                                    (argFVnames  (map VarT->name argFVs))
                                    (notInArgFVs (λe.let ((eName  (VarT->name e))
                                                          (found? (exists (λn.eq? eName n) argFVnames))
                                                         )
                                                   (not found)
                                                 )
                                    )
                                    (funcFVs     (filter notInArgFVs (self func)))
                                   )
                                (foldl (swap-args cons) argFVs funcFVs)
                              )
             )
             ((LamT var body) (let ((lbinder    (VarT->name var))
                                    (ne-binder? (λv.(not (eq? (VarT->name v) lbinder))))
                                    (bodyFVs    (self body)))
                                (filter ne-binder? bodyFVs)
                              )
             )
             (error (~ "unknown TTerm" (Term->Str t)))
           )
        )
ENDOFLAMBDA
    -> TTerm $t -->TList{
        case-Term($t,
            VarT   => -> Mu { $cons($t, $nil) },
            ConstT => $K1nil,
            AppT   => -> TTerm $func, TTerm $arg {
                my $argFVs      = &self($arg);
                my $argFVnames  = $map($VarT2name, $argFVs);
                my $notInArgFVs = -> $e { 
                    my $eName = $VarT2name($e);
                    my $found = $exists(-> $n { convertP6Bool2TBool($eName eq $n) }, $argFVnames);
                    $not($found)
                };
                my $funcFVs     = $filter($notInArgFVs, &self($func));
                $foldl($swap-args($cons), $argFVs, $funcFVs);

                #my $argFVs      = &self($arg);
                #my $notInArgFVs = -> $var { 
                #    my $found = $exists($Term-eq($var), $argFVs);
                #    $not($found)
                #};
                #my $funcFVs     = $filter($notInArgFVs, &self($func));
                #$foldl($swap-args($cons), $argFVs, $funcFVs);
            },
            LamT   => -> TTerm $var, TTerm $body {
                my $lbName      = $VarT2name($var);
                my $isnt-binder = -> $e { convertP6Bool2TBool($VarT2name($e) ne $lbName) };
                $filter($isnt-binder, &self($body));

                #$filter($B($not, $Term-eq($var)), &self($body));
            }
        );
    }
)});


constant $free-vars-internal = $Y(-> &self { lambdaFn(
    'free-vars-internal', 'NYI',
    -> TList:D $bindersAbove, TList:D $results, TTerm:D $t -->TList{
        my $K1results = -> Mu { $results };
        case-Term($t,
            ConstT => $K1results,   # t is a ConstT ~> leave results as is
            VarT => -> Str:D $varName {
                my $eqVar = -> TTerm:D $var {
                    convertP6Bool2TBool($varName eq $VarT2name($var))
                };
                $_if( $exists($eqVar, $bindersAbove),
                    $K1results,     # don't add bound variable (ie leave results as is)
                    -> Mu {
                        $_if( $exists($eqVar, $results),
                            $K1results,     # don't make duplicates (ie leave results as is)
                            -> Mu { $cons($t, $results) }
                        )
                    }
                )
            },
            AppT => -> TTerm:D $func, TTerm:D $arg {    # t is an AppT
                my $freeInArg = &self($bindersAbove, $results, $arg);
                &self($bindersAbove, $freeInArg, $func);
            },
            LamT => -> TTerm:D $var, TTerm:D $body {    # t is a LamT
                &self($cons($var, $bindersAbove), $results, $body);
            }
        )
    }
)});

constant $free-vars is export = lambdaFn('free-vars', 'free-vars-internal nil nil', $free-vars-internal($nil, $nil));
