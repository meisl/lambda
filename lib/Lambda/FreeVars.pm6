use v6;

use Lambda::Base;
use Lambda::BaseP6;
use Lambda::Boolean;
use Lambda::MaybeADT;
use Lambda::ListADT;
use Lambda::TermADT;

use Lambda::Conversion::Bool-conv;


constant $is-free-varName is export = $Y(lambdaFn(
    'free-varName?', 
 q:to/ENDOFLAMBDA/,
    λself.λvar.λt.
        (case t
            (((ConstT val)    #false)
             ((VarT name)     (eq? name (VarT->name var)))
             ((AppT func arg) (_or (self var func) (self var arg)))
             ((LamT v body)   (_and (not (eq? v var)) (self var body)))
            )
            (error (~ "unknown TTerm" (Term->Str t)))
        )
ENDOFLAMBDA
    -> &self {
        -> $equalsVarName, TTerm $t {
            $destruct-Term($t,
                $equalsVarName,                 # t is a VarT
                -> TTerm $func, TTerm $arg {    # t is an AppT
                    $_if( &self($equalsVarName, $func),       # short-circuit OR
                        $K1true,
                        -> Mu { &self($equalsVarName, $arg) }
                    )
                },
                -> TTerm $lamVar, TTerm $body { # t is a LamT
                    $_if( $equalsVarName($VarT2name($lamVar)),
                        $K1false,
                        -> Mu { &self($equalsVarName, $body) }
                    )
                },
                $K1false    # t is a ConstT
            );
        }
    }
));

constant $is-free is export = lambdaFn(
    'free?', 'λvar.free-varName (Str-eq? (VarT->name var))',  # free-varName (B Str-eq? VarT->name)
    -> TTerm $var {
        my $varName = $VarT2name($var);
        my $equalsVarName = -> Str $name {
            convertP6Bool2TBool( $varName eq $name )
        };
        $is-free-varName($equalsVarName);
    }
);

constant $is-free-under is export = $Y(lambdaFn(
    'free-under?', 
 q:to/ENDOFLAMBDA/,
    λself.λvar.λbinder.λt.
        (case t ; TODO: case -> cascaded if
            (((ConstT val)    #false)
             ((VarT name)     #false)
             ((AppT func arg) (_or (self var binder func) (self var binder arg)))
             ((LamT v body)   (let ((vName  (VarT->name var))
                                    (bName  (VarT->name binder))
                                    (lbName (VarT->name v)))
                                (_and
                                  (not (eq? lbName vName))
                                  (_if (eq? lbName bName)
                                    (free? var body)
                                    (self var binder body)
                                  )
                                )
                              )
             )
            )
            (error (~ "unknown TTerm" (Term->Str t)))
        )
ENDOFLAMBDA
    -> &self {
        -> TTerm $var, TTerm $binder, TTerm $t {
            $destruct-Term($t,
                $K1false,                   #   t is a VarT
                -> TTerm $func, $arg {      #   t is an AppT
                    $_if( &self($var, $binder, $func),  # short-circuit OR
                        $K1true,
                        -> Mu { &self($var, $binder, $arg) }
                    )
                },
                -> TTerm $lamVar, $body {   #   t is an AppT
                    my $lamVarName = $VarT2name($lamVar);
                    my $equalsLamVarName = -> Str $name {
                        convertP6Bool2TBool($lamVarName eq $name)
                    };
                    my $vName    = $VarT2name($var);
                    $_if( $equalsLamVarName($vName),
                        $K1false,               # if the λ binds the var then it's not free anywhere in the λ's body
                        -> Mu {
                            my $bName = $VarT2name($binder);
                            $_if( $equalsLamVarName($bName),     # or else, if the binder is the λ's var then...
                                -> Mu { $is-free($var, $body) },       # $var is free under $binder if $var is free in the λ's body
                                -> Mu { &self($var, $binder, $body) }  # otherwise it depends on the λ's body
                            )
                        },
                    );
                },
                $K1false                    #   t is a ConstT
            );
        }
    }
));


constant $free-var is export = $Y(lambdaFn(
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
    -> &self {
        -> Str:D $name, TTerm $t {
            if convertTBool2P6Bool($is-ConstT($t)) {
                $None
            } elsif convertTBool2P6Bool($is-VarT($t)) {
                $_if( convertP6Bool2TBool($VarT2name($t) eq $name),
                    -> $_ { $Some($t) },
                    -> $_ { $None }
                )
            } elsif convertTBool2P6Bool($is-AppT($t)) {
                my $fromFunc = &self($name, $AppT2func($t));
                $_if( $is-Some($fromFunc),
                    -> $_ { $fromFunc },
                    -> $_ { &self($name, $AppT2arg($t)) }
                )
            } elsif convertTBool2P6Bool($is-LamT($t)) {
                $_if( convertP6Bool2TBool($VarT2name($LamT2var($t)) eq $name),
                    -> $_ { $None },
                    -> $_ { &self($name, $LamT2body($t)) }
                )
            } else {
                die "fell off type-dispatch with type " ~ $t.WHAT.perl
            }
        }
    }
));


constant $___free-vars is export = $Y(lambdaFn(
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
    -> &self {
        -> TTerm $t -->TList{
            $destruct-Term($t,
                -> Mu { $cons($t, $nil) },      # t is a VarT
                -> TTerm $func, TTerm $arg {    # t is an AppT
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
                -> TTerm $var, TTerm $body {    # t is a LamT
                    my $lbName      = $VarT2name($var);
                    my $isnt-binder = -> $e { convertP6Bool2TBool($VarT2name($e) ne $lbName) };
                    $filter($isnt-binder, &self($body));

                    #$filter($B($not, $Term-eq($var)), &self($body));
                },
                $K1nil                          # t is a ConstT
            );
        }
    }
));


constant $free-vars-internal = $Y(lambdaFn(
    'free-vars-internal', '',
    -> &self {
        -> TList:D $ignore, TList:D $results, TTerm:D $t -->TList{
            my $K1results = -> Mu { $results };
            $destruct-Term($t,
                -> Str:D $varName {                 # t is a VarT
                    my $eqVar = -> TTerm:D $var {
                        convertP6Bool2TBool($varName eq $VarT2name($var))
                    };
                    $_if( $exists($eqVar, $ignore),
                        $K1results,     # don't make duplicates (ie leave results as is)
                        -> Mu { $cons($t, $results) }
                    );
                },
                -> TTerm:D $func, TTerm:D $arg {    # t is an AppT
                    my $freeInArg = &self($ignore, $results, $arg);
                    # freeInArg possibly contains more stuff to be ignored (ie results plus a prefix)
                    # but ignore may contain some vars which are not in there (ie binders from lambdas above):
                    my $newIgnore = $foldl($swap-args($cons), $freeInArg, $ignore);
                    &self($newIgnore, $freeInArg, $func);
                },
                -> TTerm:D $var, TTerm:D $body {    # t is a LamT
                    &self($cons($var, $ignore), $results, $body);
                },
                $K1results                          # t is a ConstT ~> leave results as is
            );
        }
    }
));

constant $free-vars is export = lambdaFn('free-vars', 'free-vars-internal nil nil', $free-vars-internal($nil, $nil));
