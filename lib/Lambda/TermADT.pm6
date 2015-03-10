use v6;

use Lambda::Base;
use Lambda::BaseP6;
use Lambda::Boolean;
use Lambda::String;
use Lambda::ListADT;

use Lambda::P6Currying;
use Lambda::ADT_auto;

use Lambda::Conversion::Bool-conv;

module Lambda::TermADT;


role TTerm does ADT is export {
    our $repr is export = ADTRepr.new(TTerm,
        VarT   => 1,    # name:Str
        AppT   => 2,    # func:Term  arg:Term
        LamT   => 2,    # var:VarT   body:Term
        ConstT => 1     # value:_
    );
    method repr { $repr }
}

# pattern-matching ------------------------------------------------------------

our &case-Term is export = makeMatcher(TTerm);


constant $on-VarT is export = lambdaFn(
    'on-VarT', 'λthenFn.λelseFn.λterm.let ((e1 λ_.elseFn term) (e2 λ_.e1)) (term thenFn e2 e2 e1)',
    -> &thenFn, &elseFn {
        my $lambdaExpr = "on-VarT {&thenFn.lambda} {&elseFn.lambda}";
        lambdaFn(
            Str, $lambdaExpr,
            -> TTerm $term {
                my $else1 = -> Mu { &elseFn($term) };
                my $else2 = -> Mu, Mu { &elseFn($term) };   #   $K($else1);     #   
                case-Term($term,
                    VarT   => &thenFn,
                    AppT   => $else2,
                    LamT   => $else2,
                    ConstT => $else1
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
                my $else2 = -> Mu, Mu { &elseFn($term) };   #   $K($else1);     #   
                case-Term($term,
                    VarT   => $else1,
                    AppT   => &thenFn,
                    LamT   => $else2,
                    ConstT => $else1
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
                my $else2 = -> Mu, Mu { &elseFn($term) };   #   $K($else1);     #   
                case-Term($term,
                    VarT   => $else1,
                    AppT   => $else2,
                    LamT   => &thenFn,
                    ConstT => $else1
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
                my $else2 = -> Mu, Mu { &elseFn($term) };   #   $K($else1);     #   
                case-Term($term,
                    VarT   => $else1,
                    AppT   => $else2,
                    LamT   => $else2,
                    ConstT => &thenFn
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
    -> Str:D $name -->TTerm{
        my $out = %names2vars{$name};
        unless $out.defined {
            $out = lambdaFn(
                Str, { "(VarT {$name.perl})" },
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
    -> TTerm:D $func, TTerm:D $arg -->TTerm{
        lambdaFn(
            Str, { "(AppT $func $arg)" },
            -> &onVarT, &onAppT, &onLamT, &onConstT { &onAppT($func, $arg) }
        ) does TTerm;
    }
);

# LamT: Term -> Term -> (Str -> a) -> (Term -> Term -> b) -> (Term -> Term -> c) -> (* -> d) -> c
constant $LamT is export = lambdaFn(
    'LamT', 'λvar.λbody.λonVarT.λonAppT.λonLamT.λonConstT.onLamT var body',
    {   my $e = -> $t { die "first arg to LamT ctor must be a VarT - got instead $t" };
        -> TTerm:D $var, TTerm:D $body -->TTerm{
            case-Term($var,
                VarT => -> Str $name {
                    lambdaFn(
                        Str, { "(LamT $var $body)" },
                        -> &onVarT, &onAppT, &onLamT, &onConstT { &onLamT($var, $body) }
                    ) does TTerm;
            
                },
                AppT   => -> TTerm $func, TTerm $arg  { $e($var) },
                LamT   => -> TTerm $var,  TTerm $body { $e($var) },
                ConstT => -> Any $value               { $e($var) }
            )
        }
    }()
);

# ConstT: Term -> Term -> (Str -> a) -> (Term -> Term -> b) -> (Term -> Term -> c) -> (* -> d) -> d
constant $ConstT is export = lambdaFn(
    'ConstT', 'λvalue.λonVarT.λonAppT.λonLamT.λonConstT.onConstT value',
    -> $value -->TTerm{
        lambdaFn(
            Str, { "(ConstT {$value.perl})" },
            -> &onVarT, &onAppT, &onLamT, &onConstT { &onConstT($value) }
        ) does TTerm;
    }
);


constant $Term-eq is export = $Y(-> &self { lambdaFn(
    'Term-eq?', 'NYI',
    -> TTerm $s, TTerm $t -->TBool{
        case-Term($s,
            VarT => -> Str $sName {
                case-Term($t,
                    VarT => $Str-eq($sName),
                    AppT => $K2false,
                    LamT => $K2false,
                    ConstT => $K1false
                )
            },

            AppT => -> TTerm $sFunc, TTerm $sArg {
                case-Term($t,
                    VarT => $K1false,
                    AppT => -> TTerm $tFunc, TTerm $tArg {
                        $_if(&self($sFunc, $tFunc),
                            -> Mu { &self($sArg,  $tArg) },
                            $K1false
                        )
                        #$_and(
                        #    &self($sFunc, $tFunc),
                        #    &self($sArg,  $tArg),
                        #)
                    },
                    LamT => $K2false,
                    ConstT => $K1false
                )
            },

            LamT => -> TTerm $sVar, TTerm $sBody {
                case-Term($t,
                    VarT => $K1false,
                    AppT => $K2false,
                    LamT => -> TTerm $tVar, TTerm $tBody {
                        $_if(&self($sVar, $tVar),
                            -> Mu { &self($sBody,  $tBody) },
                            $K1false
                        )
                        #$_and(
                        #    &self($sVar,  $tVar),
                        #    &self($sBody, $tBody)
                        #)
                    },
                    ConstT => $K1false
                )
            },
            ConstT => -> Any $sValue {
                case-Term($t,
                    VarT => $K1false,
                    AppT => $K2false,
                    LamT => $K2false,
                    ConstT => -> Any $tValue { die "NYI: equality test for $sValue, $tValue" }
                )
            },

        )
    }
)});

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
    'Term->Str', 'λt.error "NYI"',
    -> TTerm:D $t { $t.Str }
);


# functions on Term -----------------------------------------------------------

constant $Term2source is export = $Y(-> &self { lambdaFn(
    'Term->source', 'λt.(error "NYI")',
    -> TTerm:D $t -->Str{
        case-Term($t,
            VarT => $I, # just return the name
            AppT => -> TTerm $func, TTerm$arg -->Str{
                my $fSrc = &self($func);
                my $aSrc = &self($arg);
                "($fSrc $aSrc)"
            },
            LamT => -> TTerm $var, TTerm $body -->Str{
                my $vSrc = &self($var);
                my $bSrc = &self($body);
                "(λ$vSrc.$bSrc)"

            },
            ConstT => -> Any $val -->Str{
                $val.perl    #   $B($pi1o2, *.perl)
            }
        )
    }
)});


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
        case-Term($t,
            ConstT => $K1nil,
            VarT   => $K1nil,
            AppT => -> $f, $a {
                $cons($f, $cons($a, $nil))
            },
            LamT => -> $v, $b {
                $cons($v, $cons($b, $nil))
            }
        )
    }
);


constant $Term2size is export = $Y(-> &self { lambdaFn(
    'Term->size', 'λself.λt.(foldl (λacc.λchild.(+ acc (self child))) 1 (Term->children t))',
    -> TTerm:D $t -->Int{
        $foldl(-> $acc, $child { $acc + &self($child) }, 1, $Term2children($t));
    }
)});


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

# selfAppOfVar?: Term -> Term -> Bool
constant $is-selfAppOfVar is export =
    $on-VarT(
        -> Str $varName {
            my $equalsVarName = -> Str $s {
                convertP6Bool2TBool($varName eq $s)    # TODO: dispense with convertP6Bool2TBool
            } does lambda('Str-eq? "' ~ $varName ~ '"');
            $on-AppT(
                $on-VarT(   # takes the AppT's func
                    -> Str $funcName {
                        $_if( $equalsVarName($funcName),
                            -> Mu {
                                $on-VarT(   # take the AppT's arg
                                    $equalsVarName,
                                    $K1false
                                )
                            },
                            $K2false    # eat up both, the dummy arg from _if and the arg from AppT
                        )
                    } does lambda("(λfuncName.if ({$equalsVarName.lambda} funcName) (on-VarT ({$equalsVarName.lambda}) λ_.#false) λ_.#false)"),
                    $K2false    # eat up both, the func and arg from AppT
                ),
                $K1false
            )
        } does lambda('bar'),
        $K2false    # eat up outermost non-VarT term and return a function which takes another term and returns #false
    ) does Definition('selfAppOfVar?')
;


constant $is-omega is export =
    $on-LamT(
        $is-selfAppOfVar,
        $K1false
    ) does Definition('ω?')
;


constant $is-Omega is export =
    $on-AppT(
        -> TTerm $func, TTerm $arg {
            $_if( $is-omega($func),
                -> Mu { $is-omega($arg) },
                $K1false
            )
        } does lambda('λfunc.λarg.and (ω? func) (ω? arg)'),
        $K1false
    ) does Definition('Ω?')
;


constant $fresh-var-for is export = {
    my $nextAlphaNr = 1;

    my role AlphaVarT[TTerm:D $for, Str:D $gist] {
        method for  { $for  }
        method gist { $gist }
    }

    lambdaFn(
        'fresh-var-for', 'λfor.error "NYI"',
        -> TTerm $for -->TTerm{
            #say $nextAlphaNr;
            my $vName = 'α' ~ $nextAlphaNr;
            $nextAlphaNr++;
            my $v = $VarT($vName);
            $v ~~ TTerm or die $v.perl;
            if $for.defined {
                my $forStr = ($for ~~ AlphaVarT)
                    ?? $for.gist
                    !! $VarT2name($for);
                my $gistStr = $vName ~ "[/$forStr]";
                $_if( $is-VarT($for),
                    -> Mu { $v does AlphaVarT[$for, $gistStr] },
                    -> Mu { die "can make fresh var for another var but not for $for" }
                )
            }
            $v;
        }
    );
}();
