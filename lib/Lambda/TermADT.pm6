use v6;

use Lambda::Base;
use Lambda::BaseP6;
use Lambda::Boolean;
use Lambda::ListADT;

use Lambda::P6Currying;

use Lambda::Conversion::Bool-conv;


module Lambda::TermADT;
# data Term = VarT   name:Str
#           | AppT   func:Term  arg:Term
#           | LamT   var:VarT   body:Term
#           | ConstT value:_
role TTerm is export {
}


my constant $K1false = $K($false);
my constant $K1true  = $K($true);
my constant $K2false = $K($K1false);
my constant $K2true  = $K($K1true);


# pattern-matching ------------------------------------------------------------

constant $destruct-Term is export = lambdaFn(
    'destruct-Term', 'λterm.λcases.term cases',
    -> TTerm:D $t, &onVarT, &onAppT, &onLamT, &onConstT { 
        $t(&onVarT, &onAppT, &onLamT, &onConstT)
    }
);

constant $on-VarT is export = lambdaFn(
    'on-VarT', 'λthenFn.λelseFn.λterm.let ((e1 λ_.elseFn term) (e2 λ_.e1)) (term thenFn e2 e2 e1)',
    -> &thenFn, &elseFn {
        my $lambdaExpr = "on-VarT {&thenFn.lambda} {&elseFn.lambda}";
        lambdaFn(
            Str, $lambdaExpr,
            -> TTerm $term {
                my $else1 = -> Mu { &elseFn($term) };
                my $else2 = $K($else1);
                $destruct-Term($term,
                    &thenFn,
                    $else2,
                    $else2,
                    $else1
                )
            }
        )
    }
);

constant $on-AppT is export = lambdaFn(
    'on-AppT', 'λthenFn.λelseFn.λterm.let ((e1 λ_.elseFn term) (e2 λ_.e1)) (term e1 thenFn e2 e1)',
    -> &thenFn, &elseFn {
        my $lambdaExpr = "on-AppT {&thenFn.lambda} {&elseFn.lambda}";
        lambdaFn(
            Str, $lambdaExpr,
            -> TTerm $term {
                my $else1 = -> Mu { &elseFn($term) };
                my $else2 = $K($else1);
                $destruct-Term($term,
                    $else1,
                    &thenFn,
                    $else2,
                    $else1
                )
            }
        )
    }
);

constant $on-LamT is export = lambdaFn(
    'on-LamT', 'λthenFn.λelseFn.λterm.let ((e1 λ_.elseFn term) (e2 λ_.e1)) (term e1 e2 thenFn e1)',
    -> &thenFn, &elseFn {
        my $lambdaExpr = "on-LamT {&thenFn.lambda} {&elseFn.lambda}";
        lambdaFn(
            Str, $lambdaExpr,
            -> TTerm $term {
                my $else1 = -> Mu { &elseFn($term) };
                my $else2 = $K($else1);
                $destruct-Term($term,
                    $else1,
                    $else2,
                    &thenFn,
                    $else1
                )
            }
        )
    }
);

constant $on-ConstT is export = lambdaFn(
    'on-ConstT', 'λthenFn.λelseFn.λterm.let ((e1 λ_.elseFn term) (e2 λ_.e1)) (term e1 e2 e2 thenFn)',
    -> &thenFn, &elseFn {
        my $lambdaExpr = "on-ConstT {&thenFn.lambda} {&elseFn.lambda}";
        lambdaFn(
            Str, $lambdaExpr,
            -> TTerm $term {
                my $else1 = -> Mu { &elseFn($term) };
                my $else2 = $K($else1);
                $destruct-Term($term,
                    $else1,
                    $else2,
                    $else2,
                    &thenFn
                )
            }
        )
    }
);



# constructors ----------------------------------------------------------------

# must make the hash a constant (it's still mutable though)
# in order to have it real global
my constant %names2vars = %();

# VarT: Str -> (Str -> a) -> (Term -> Term -> b) -> (Term -> Term -> c) -> (* -> d) -> a
constant $VarT is export = lambdaFn(
    'VarT', 'λname.λonVarT.λonAppT.λonLamT.λonConstT.onVarT name',
    -> Str:D $name {
        my $out = %names2vars{$name};
        unless $out.defined {
            my $nameStr = $name.perl;
            $out = lambdaFn(
                Str, "(VarT $nameStr)",
                -> &onVarT, &onAppT, &onLamT, &onConstT { &onVarT($name) }
            ) does TTerm;
            %names2vars{$name} = $out;
#            note '>>>> ' ~ %names2vars.elems ~ ' vars now: ' ~ %names2vars;
        }
        $out;
    }
);

# AppT: Term -> Term -> (Str -> a) -> (Term -> Term -> b) -> (Term -> Term -> c) -> (* -> d) -> b
constant $AppT is export = lambdaFn(
    'AppT', 'λfunc.λarg.λonVarT.λonAppT.λonLamT.λonConstT.onAppT func arg',
    -> TTerm:D $func, TTerm:D $arg {
        lambdaFn(
            Str, "(AppT $func $arg)",
            -> &onVarT, &onAppT, &onLamT, &onConstT { &onAppT($func, $arg) }
        ) does TTerm;
    }
);

# LamT: Term -> Term -> (Str -> a) -> (Term -> Term -> b) -> (Term -> Term -> c) -> (* -> d) -> c
constant $LamT is export = lambdaFn(
    'LamT', 'λvar.λbody.λonVarT.λonAppT.λonLamT.λonConstT.onLamT var body',
    {   my $e = -> $t { die "first arg to LamT ctor must be a VarT - got instead $t" };
        -> TTerm:D $var, TTerm:D $body {
            $destruct-Term($var,
                -> Str $name {
                    lambdaFn(
                        Str, "(LamT $var $body)",
                        -> &onVarT, &onAppT, &onLamT, &onConstT { &onLamT($var, $body) }
                    ) does TTerm;
            
                },
                -> TTerm $func, TTerm $arg  { $e($var) },
                -> TTerm $var,  TTerm $body { $e($var) },
                -> Any $value               { $e($var) }
            )
        }
    }()
);

# ConstT: Term -> Term -> (Str -> a) -> (Term -> Term -> b) -> (Term -> Term -> c) -> (* -> d) -> d
constant $ConstT is export = lambdaFn(
    'ConstT', 'λvalue.λonVarT.λonAppT.λonLamT.λonConstT.onConstT value',
    -> $value {
        my $valueStr = $value.perl;
        lambdaFn(
            Str, "(ConstT $valueStr)",
            -> &onVarT, &onAppT, &onLamT, &onConstT { &onConstT($value) }
        ) does TTerm;
    }
);


constant $Term-eq is export = $Y(lambdaFn(
    'Term-eq?', 'NYI',
    -> &self, TTerm $s, TTerm $t -->TBool{
        $destruct-Term($s,
            -> Str $sName {
                $on-VarT(
                    -> Str $tName {
                        convertP6Bool2TBool($sName eq $tName)
                    } does lambda("Str-eq? \"$sName\"" ),
                    $K1false,
                    $t
                )
                #$destruct-Term($t,
                #    -> Str $tName { convertP6Bool2TBool($sName eq $tName) },
                #    $K2false,
                #    $K2false,
                #    $K1false
                #)
            },
            -> TTerm $sFunc, TTerm $sArg {
                $on-AppT(
                    -> TTerm $tFunc, TTerm $tArg {
                        $_and(
                            &self($sFunc, $tFunc),
                            &self($sArg,  $tArg)
                        )
                    } does lambda("λtFunc.λtArg.and (Term-eq? sFunc tFunc) (Term-eq? sArg tArg)" ),
                    $K1false,
                    $t
                );
                #$destruct-Term($t,
                #    $K1false,
                #    -> TTerm $tFunc, TTerm $tArg {
                #        $_and(
                #            &self($sFunc, $tFunc),
                #            &self($sArg,  $tArg)
                #        )
                #    },
                #    $K2false,
                #    $K1false
                #)
            },
            -> TTerm $sVar, TTerm $sBody {
                $on-LamT(
                    -> TTerm $tVar, TTerm $tBody {
                        $_and(
                            &self($sVar, $tVar),
                            &self($sBody,  $tBody)
                        )
                    } does lambda("λtVar.λtBody.and (Term-eq? sVar tVar) (Term-eq? sBody tBody)" ),
                    $K1false,
                    $t
                );
                #$destruct-Term($t,
                #    $K1false,
                #    $K2false,
                #    -> TTerm $tVar, TTerm $tBody {
                #        $_and(
                #            &self($sVar,  $tVar),
                #            &self($sBody, $tBody)
                #        )
                #    },
                #    $K1false
                #)
            },
            -> Any $sValue {
                $on-ConstT(
                    -> Any $tValue {
                        die "NYI: equality test for $sValue, $tValue"
                    } does lambda("eq? \"$sValue\"" ),
                    $K1false,
                    $t
                );
                #$destruct-Term($t,
                #    $K1false,
                #    $K2false,
                #    $K2false,
                #    -> Any $tValue { die "NYI: equality test for $sValue, $tValue" }
                #)
            },

        )
    }
));



# predicates ------------------------------------------------------------------

# VarT?: Term -> Bool
constant $is-VarT is export = $on-VarT($K1true, $K1false) does Definition('VarT?');

# AppT?: Term -> Bool
constant $is-AppT is export = $on-AppT($K2true, $K1false) does Definition('AppT?');

# LamT?: Term -> Bool
constant $is-LamT is export = $on-LamT($K2true, $K1false) does Definition('LamT?');

# ConstT?: Term -> Bool
constant $is-ConstT is export = $on-ConstT($K1true, $K1false) does Definition('ConstT?');


# projections -----------------------------------------------------------------

# VarT->name: Term -> Str
constant $VarT2name is export = $on-VarT(
    $pi1o1,
    lambdaFn(
        Str, 'λterm.error (~ "cannot apply VarT->name to " (Term->Str term))',
        -> TTerm $term { die "cannot apply VarT->name to $term" }
    )
) does Definition('VarT->name');

# AppT->func: Term -> Term
constant $AppT2func is export = $on-AppT(
    $pi1o2,
    lambdaFn(
        Str, 'λterm.error (~ "cannot apply AppT->func to " (Term->Str term))',
        -> TTerm $term { die "cannot apply AppT->func to $term" }
    )
) does Definition('AppT->func');

# AppT->arg: Term -> Term
constant $AppT2arg is export = $on-AppT(
    $pi2o2,
    lambdaFn(
        Str, 'λterm.error (~ "cannot apply AppT->arg to " (Term->Str term))',
        -> TTerm $term { die "cannot apply AppT->arg to $term" }
    )
) does Definition('AppT->arg');

# LamT->var: Term -> Term
constant $LamT2var is export = $on-LamT(
    $pi1o2,
    lambdaFn(
        Str, 'λterm.error (~ "cannot apply LamT->var to " (Term->Str term))',
        -> TTerm $term { die "cannot apply LamT->var to $term" }
    )
) does Definition('LamT->var');

# LamT->body: Term -> Term
constant $LamT2body is export = $on-LamT(
    $pi2o2,
    lambdaFn(
        Str, 'λterm.error (~ "cannot apply LamT->body to " (Term->Str term))',
        -> TTerm $term { die "cannot apply LamT->body to $term" }
    )
) does Definition('LamT->body');

# ConstT->value: Term -> *
constant $ConstT2value is export = $on-ConstT(
    $pi1o1,
    lambdaFn(
        Str, 'λterm.error (~ "cannot apply ConstT->value to " (Term->Str term))',
        -> TTerm $term { die "cannot apply ConstT->value to $term" }
    )
) does Definition('ConstT->value');


# ->Str -----------------------------------------------------------------------

constant $Term2Str is export = lambdaFn(
    'Term->Str', 'λt.(error "NYI")',
    -> TTerm:D $t { $t.Str }
);


# functions on Term -----------------------------------------------------------

constant $Term2source is export = $Y(lambdaFn(
    'Term->source', 
q:to/ENDOFLAMBDA/,
    λself.λt.given-Term t
        (when-ConstT (λval.λ_.->Str val)    ; (B ->Str π2->1) = ->Str ° π2->1 = ->Str • π2->1 = ->Str·π2->1
        (when-VarT   (λname.λ_.name)        ; π2->1
        (when-AppT   (λfunc.λarg.
            (let ((fSrc (self func))
                  (aSrc (self arg))
                 )
               (~ "(" (~ fSrc (~ aSrc ")")))
            )
        )
        (when-LamT (λv.λbody.
            (let ((vSrc (self v))
                  (bSrc (self body))
                 )
               (~ "(LAMBDA" (~ vSrc (~ DOT (~ bSrc ")"))))    ; TODO: put literal lambda and dot here (once we have got string literals in the syntax)
            )
        )
        λ_.λ_.λ_.λ_.error (~ "unknown TTerm" (Term->Str t))
        ))))
ENDOFLAMBDA
    -> &self {
        -> TTerm:D $t -->Str{
            $destruct-Term($t,
                $id,                                 # onVarT
                -> TTerm $func, TTerm$arg -->Str{    # onAppT
                    my $fSrc = &self($func);
                    my $aSrc = &self($arg);
                    "($fSrc $aSrc)"
                },
                -> TTerm $var, TTerm $body -->Str{    # onLamT
                    my $vSrc = &self($var);
                    my $bSrc = &self($body);
                    "(λ$vSrc.$bSrc)"

                },
                -> Any $val -->Str{           # onConstT
                    $val.perl    #   $B($pi1o2, *.perl)
                }
            )
        }
    }
));


constant $Term2children is export = lambdaFn(
    'Term->children', 
q:to/ENDOFLAMBDA/,
    λt.given-Term t
        (when-ConstT (λ_.λ_.nil)                    ; (K (K nil))  χ2 K nil
        (when-VarT   (λ_.λ_.nil)                    ; (K (K nil))
        (when-AppT   (λf.λa.cons f (cons a nil))    ; (B (C cons) (C cons nil))
        (when-LamT   (λv.λb.cons v (cons b nil))    ; (B (C cons) (C cons nil))
        λ_.λ_.λ_.λ_.error (~ "unknown TTerm" (Term->Str t))
        ))))
ENDOFLAMBDA
    -> TTerm:D $t -->TList{
        $destruct-Term($t,
            -> $name  { $nil }, # onVarT
            -> $f, $a {         # onAppT
                $cons($f, $cons($a, $nil))
            },
            -> $v, $b {         # onLamT
                $cons($v, $cons($b, $nil))
            },
            -> $value { $nil } # onConstT
        )
    }
);


constant $Term2size is export = $Y(lambdaFn(
    'Term->size', 'λself.λt.(foldl (λacc.λchild.(+ acc (self child))) 1 (Term->children t))',
    -> &self {
        -> TTerm:D $t -->Int{
            $foldl(-> $acc, $child { $acc + &self($child) }, 1, $Term2children($t));
        }
    }
));


# (on-AppT (on-VarT λfuncName.on-VarT (Str-eq? funcName) (λ_.false) (λ_.λ_.false)) (λ_.false))
# (unless-AppT (λ_.false) (unless-VarT (λ_.λ_.false) λfuncName.unless-VarT (λ_.false) (Str-eq? funcName)))
# selfApp?: Term -> Bool
constant $is-selfApp is export = 
    $on-AppT(
        $on-VarT(   # takes the AppT's func
            -> Str $funcName {
                $on-VarT(   # take the AppT's arg
                    -> Str $argName {
                        convertP6Bool2TBool($funcName eq $argName)    # TODO: dispense with convertP6Bool2TBool
                    } does lambda('Str-eq? "' ~ $funcName ~ '"'),
                    $K1false
                )
            } does lambda('λfuncName.on-VarT (λargName.Str-eq? funcName argName) (λ_.#false)'),
            $K2false    # eat up both, the func and arg from AppT
        ),
        $K1false
    ) does Definition('selfApp?')
;


constant $is-omega is export =
    $on-LamT(
        -> TTerm $var, TTerm $body {
            $on-AppT(
                -> TTerm $f, TTerm $a {

                    #$_and($Term-eq($var, $f), $Term-eq($var, $a))
                    
                    $_if( $Term-eq($var, $f),
                        -> Mu { $Term-eq($var, $a) },
                        $K1false
                    )
                } does lambda('λfunc.λarg.if (Term-eq? var func) (Term-eq? var arg) #false'),
                $K1false,
                $body
            )
        } does lambda('λvar.λbody.on-AppT (λfunc.λarg.if (Term-eq? var func) (Term-eq? var arg) #false) λ_.#false'),
        $K1false
    ) does Definition('ω?')
;


constant $is-Omega is export =
    $on-AppT(
        -> TTerm $func, TTerm $arg {
            $_and($is-omega($func), $is-omega($arg))
        } does lambda('λfunc.λarg.and (ω? func) (ω? arg)'),
        $K1false
    ) does Definition('Ω?')
;


constant $fresh-var-for is export = {
    my $nextAlphaNr = 1;

    my role AlphaVarT {
        has TTerm:D $.for;

        method gist {
            my $forStr = ($!for ~~ AlphaVarT)
                ?? $!for.gist
                !! $VarT2name($!for);
            $VarT2name(self) ~ "[/$forStr]";
        }
    }
    lambdaFn(
        'fresh-var-for', 'λfor.error "NYI"',
        -> TTerm:D $for -->TTerm{
            say $nextAlphaNr;
            my $v = $VarT('α' ~ $nextAlphaNr);
            $v ~~ TTerm or die $v.perl;
            if $for.defined {
                $_if( $is-VarT($for),
                    -> Mu { $v does AlphaVarT(:$for) },
                    -> Mu { die "can make fresh var for another var but not for $for" }
                )
            }
            $nextAlphaNr++;
            $v;
        }
    );
}();
