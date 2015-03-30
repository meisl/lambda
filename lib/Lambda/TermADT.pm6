use v6;

use Lambda::Base;
use Lambda::BaseP6;
use Lambda::Boolean;
use Lambda::String;
use Lambda::PairADT;
use Lambda::ListADT;
use Lambda::Streams;

use Lambda::ADT_auto;

use Lambda::Conversion;

module Lambda::TermADT;


role TTerm does ADT is export {
    my $repr = ADTRepr.new(TTerm,
        VarT   => 1,    # name:Str
        AppT   => 2,    # func:Term  arg:Term
        LamT   => 2,    # var:Str   body:Term
        ConstT => 1     # value:_
    );
    method repr { $repr }
}

# pattern-matching ------------------------------------------------------------

#our &case-Term is export = makeMatcher(TTerm);

my sub checkSig(&callback, Str $cbName, *@types) is hidden_from_backtrace {
    my $s = &callback.signature;
    my @p = $s.params;
    die "invalid signature for $cbName callback: {$s.perl}"
        unless False
        || (@types == 1) && ( (&callback === $pi1o1) || (&callback === $I    ) )
        || (@types == 2) && ( (&callback === $pi1o2) || (&callback === $pi2o2) )
        || (@types == 3) && ( (&callback === $pi1o3) || (&callback === $pi2o3) || (&callback === $pi3o3) )
        || ($s.arity == +@types)
            && (@p Z @types).map(
                -> $p, $t { 
                    ($p.type.perl eq $t.perl) && ($p.name !~~ Nil)
                 || ($p.type.perl eq 'Mu'   ) && ($p.name  ~~ Nil)
                }).all
    ;
}

our sub case-Term(TTerm:D $term, :VarT(&onVarT)!, :AppT(&onAppT)!, :LamT(&onLamT)!, :ConstT(&onConstT)!) is hidden_from_backtrace is export {
    #checkSig(&onVarT, 'VarT', Str);
    #checkSig(&onLamT, 'LamT', Str, TTerm);
    #checkSig(&onAppT, 'AppT', TTerm, TTerm);
    #checkSig(&onConstT, 'ConstT', Any);

    $term(&onVarT, &onAppT, &onLamT, &onConstT);
};


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
                Str, { "(VarT {$name.perl})" }, #   "λa.λb.λc.λd.a {$name.perl}",     #       
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

my constant $LamT-error = -> $t { die "first arg to LamT ctor must be a VarT - got instead $t" };

# LamT: Term -> Term -> (Str -> a) -> (Term -> Term -> b) -> (Term -> Term -> c) -> (* -> d) -> c
constant $LamT is export = lambdaFn(
    'LamT', 'λvar.λbody.λonVarT.λonAppT.λonLamT.λonConstT.onLamT var body',
    -> Str:D $varName, TTerm:D $body -->TTerm{
        lambdaFn(
            Str, { "(LamT {$varName.perl} $body)" },
            -> &onVarT, &onAppT, &onLamT, &onConstT { &onLamT($varName, $body) }
        ) does TTerm;
    }
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
                    VarT => -> Str $vName { $Str-eq($sName, $vName) },
                    AppT => $K2false,
                    LamT => $K2false,
                    ConstT => $K1false
                )
            },

            AppT => -> TTerm $sFunc, TTerm $sArg {
                case-Term($t,
                    VarT => $K1false,
                    AppT => -> TTerm $tFunc, TTerm $tArg {
                        _if_( &self($sFunc, $tFunc), # short-circuit AND
                            { &self($sArg,  $tArg) },
                            $false
                        )
                    },
                    LamT => $K2false,
                    ConstT => $K1false
                )
            },

            LamT => -> Str $sVarName, TTerm $sBody {
                case-Term($t,
                    VarT => $K1false,
                    AppT => $K2false,
                    LamT => -> Str $tVarName, TTerm $tBody {
                        _if_( $Str-eq($sVarName, $tVarName), # short-circuit AND
                            { &self($sBody,  $tBody) },
                            $false
                        )
                    },
                    ConstT => $K1false
                )
            },
            ConstT => -> Any $sValue {
                case-Term($t,
                    VarT => $K1false,
                    AppT => $K2false,
                    LamT => $K2false,
                    ConstT => -> Any $tValue {
                        if $sValue ~~ Str {
                            if $tValue ~~ Str {
                                $Str-eq($sValue, $tValue);
                            } elsif $tValue ~~ Int {
                                $false;
                            } else {
                                die "NYI: equality test for ConstT with value of type {$tValue.WHAT.perl}";
                            }
                        } elsif $sValue ~~ Int {
                            if $tValue ~~ Str {
                                $false;
                            } elsif $tValue ~~ Int {
                                die "NYI: equality test for two Int constants {$sValue.perl}, {$tValue.perl}";
                            } else {
                                die "NYI: equality test for ConstT with value of type {$tValue.WHAT.perl}";
                            }
                        } else {    # sValue is neither of type Str nor of type Int
                            die "NYI: equality test for ConstT with value of type {$sValue.WHAT.perl}";
                        }
                    }
                )
            },

        )
    }
)});

# predicates ------------------------------------------------------------------

# VarT?: Term -> Bool
constant $is-VarT is export = lambdaFn(
    'VarT?', 'not yet implemented', 
    -> TTerm:D $t { case-Term($t,
        VarT   => $K1true,
        AppT   => $K2false,
        LamT   => $K2false,
        ConstT => $K1false
    )}
);

# AppT?: Term -> Bool
constant $is-AppT is export = lambdaFn(
    'AppT?', 'not yet implemented', 
    -> TTerm:D $t { case-Term($t,
        VarT   => $K1false,
        AppT   => $K2true,
        LamT   => $K2false,
        ConstT => $K1false
    )}
);

# LamT?: Term -> Bool
constant $is-LamT is export = lambdaFn(
    'LamT?', 'not yet implemented', 
    -> TTerm:D $t { case-Term($t,
        VarT   => $K1false,
        AppT   => $K2false,
        LamT   => $K2true,
        ConstT => $K1false
    )}
);

# ConstT?: Term -> Bool
constant $is-ConstT is export = lambdaFn(
    'ConstT?', 'not yet implemented', 
    -> TTerm:D $t { case-Term($t,
        VarT   => $K1false,
        AppT   => $K2false,
        LamT   => $K2false,
        ConstT => $K1true
    )}
);


# projections -----------------------------------------------------------------
my constant $prj-error = lambdaFn(
    'prj-error', 'λfnName.λterm.error (~ (~ (~ "cannot apply " fnName) " to ") (Term->Str term)))',
    -> Str $fnName, TTerm $term { die "cannot apply $fnName to $term" }
);

# VarT->name: Term -> Str
constant $VarT2name is export = lambdaFn(
    'VarT->name', 'not yet implemented',
    -> TTerm:D $t -->Str{ case-Term($t, 
        VarT   => $pi1o1,
        AppT   => -> Mu, Mu { $prj-error('VarT->name', $t) },
        LamT   => -> Mu, Mu { $prj-error('VarT->name', $t) },
        ConstT => -> Mu     { $prj-error('VarT->name', $t) }
    ) }
);

# AppT->func: Term -> Term
constant $AppT2func is export = lambdaFn(
    'AppT->func', 'not yet implemented',
    -> TTerm:D $t -->TTerm{ case-Term($t, 
        VarT   => -> Mu     { $prj-error('AppT->func', $t) },
        AppT   => $pi1o2,
        LamT   => -> Mu, Mu { $prj-error('AppT->func', $t) },
        ConstT => -> Mu     { $prj-error('AppT->func', $t) }
    ) }
);

# AppT->arg: Term -> Term
constant $AppT2arg is export = lambdaFn(
    'AppT->arg', 'not yet implemented',
    -> TTerm:D $t -->TTerm{ case-Term($t, 
        VarT   => -> Mu     { $prj-error('AppT->arg', $t) },
        AppT   => $pi2o2,
        LamT   => -> Mu, Mu { $prj-error('AppT->arg', $t) },
        ConstT => -> Mu     { $prj-error('AppT->arg', $t) }
    ) }
);

# LamT->var: Term -> Term
constant $LamT2var is export = lambdaFn(    # TODO: rename LamT2var to LamT2binderName
    'LamT->var', 'not yet implemented',
    -> TTerm:D $t -->TTerm{ case-Term($t, 
        VarT   => -> Mu     { $prj-error('LamT->var', $t) },
        AppT   => -> Mu, Mu { $prj-error('LamT->var', $t) },
        LamT   => $pi1o2,
        ConstT => -> Mu     { $prj-error('LamT->var', $t) }
    ) }
);

# LamT->body: Term -> Term
constant $LamT2body is export = lambdaFn(
    'LamT->body', 'not yet implemented',
    -> TTerm:D $t -->TTerm{ case-Term($t, 
        VarT   => -> Mu     { $prj-error('LamT->body', $t) },
        AppT   => -> Mu, Mu { $prj-error('LamT->body', $t) },
        LamT   => $pi2o2,
        ConstT => -> Mu     { $prj-error('LamT->body', $t) }
    ) }
);

# ConstT->value: Term -> *
constant $ConstT2value is export = lambdaFn(
    'ConstT->value', 'not yet implemented',
    -> TTerm:D $t -->Any{ case-Term($t, 
        VarT   => -> Mu     { $prj-error('ConstT->value', $t) },
        AppT   => -> Mu, Mu { $prj-error('ConstT->value', $t) },
        LamT   => -> Mu, Mu { $prj-error('ConstT->value', $t) },
        ConstT => $pi1o1
    ) }
);


# ->Str -----------------------------------------------------------------------

constant $Term2Str is export = lambdaFn(
    'Term->Str', 'λt.error "NYI"',
    -> TTerm:D $t { $t.Str }
);


# functions on Term -----------------------------------------------------------


# Term->source: Term -> Str
# fully parenthesized lambda expr from Term
constant $Term2source is export = $Y(-> &self { lambdaFn(
    'Term->source', 'λt.error "NYI"',
    -> TTerm:D $t -->Str{
        case-Term($t,
            VarT => $I, # just return the name
            AppT => -> TTerm $func, TTerm $arg {
                my $fSrc = &self($func);
                my $aSrc = &self($arg);
                "($fSrc $aSrc)"
            },
            LamT => -> Str $binderName, TTerm $body {
                my $bodySrc = &self($body);
                "(λ$binderName.$bodySrc)"

            },
            ConstT => -> Any $val {
                $val.perl    #   $B($pi1o2, *.perl)
            }
        )
    }
)});

constant $Term2srcFull is export = $Term2source but Definition('Term->srcFull');


# Term->srcLesser-internal: Term -> Pair Bool Str
# lambda expr from Term with (reasonably) fewer parentheses;
# in particular, the outermost parentheses are always omitted
# --
# The first component of the returned Pair indicates whether
# the second (a Str) starts with an opening parenthesis "(".
constant $Term2srcLesser-internal is export = $Y(-> &self { lambdaFn(
    'Term->srcLesser-internal', 'λt.error "NYI"',
    -> TTerm:D $t -->TPair{
        case-Term($t,
            ConstT => -> Any $val          { $Pair($false, $val.perl) },
            VarT   => -> Str $n            { $Pair($false, $n       ) },
            LamT   => -> Str $vn, TTerm $b { $Pair($false, 'λ' ~ $vn ~ '.' ~ $snd(&self($b))) },
            AppT   => -> TTerm $f, TTerm $a {
                my $a2str = $snd(&self($a));
                my $right = case-Term($a,
                    LamT   => -> Mu, Mu { '(' ~ $a2str ~ ')' },
                    AppT   => -> Mu, Mu { '(' ~ $a2str ~ ')' },
                    VarT   => -> Mu     {       $a2str       },
                    ConstT => -> Mu     {       $a2str       }
                );
                my $f2 = &self($f);
                my $f2str = $snd($f2);
                case-Term($f,
                    LamT   => -> Mu, Mu { $Pair($true,    '(' ~ $f2str ~ ')' ~ ' ' ~ $right) },
                    AppT   => -> Mu, Mu { $Pair($fst($f2),      $f2str       ~ ' ' ~ $right) },
                    VarT   => -> Mu     { $Pair($fst($f2),      $f2str       ~ ' ' ~ $right) },
                    ConstT => -> Mu     { $Pair($fst($f2),      $f2str       ~ ' ' ~ $right) }
                );
            }
        )
    }
)});

# Term->srcLesser: Term -> Str
# lambda expr from Term with (reasonably) fewer parentheses;
# in particular, the outermost parentheses are always omitted
constant $Term2srcLesser is export = lambdaFn(
    'Term->srcLesser', 'λt.error "NYI"',
    -> TTerm $t -->Str{ $snd($Term2srcLesser-internal($t)) }
);
# TODO: save some Pair constructions and destructions by mutual recursive definition of Term->srcLesser and Term->srcLesser-internal


# Term->srcLess: Term -> Str
# lambda expr from Term like Term->srcLesser but with outer parens around some applications
constant $Term2srcLess is export = lambdaFn(
    'Term->srcLess', 'λt.error "NYI"',
    -> TTerm:D $t -->Str{
        case-Term($t,
            ConstT => -> Mu     { $Term2srcLesser($t) },
            VarT   => -> Mu     { $Term2srcLesser($t) },
            LamT   => -> Mu, Mu { $Term2srcLesser($t) },
            AppT   => -> Mu, Mu {
                my TPair $p = $Term2srcLesser-internal($t);
                my Str   $s = $snd($p);
                _if_( $fst($p),
                    { $s },
                    { '(' ~ $s ~ ')' }
                );
            }
        )
    }
);

constant $Term2sourceP6 is export = $Y(-> &self { lambdaFn(
    'Term->sourceP6', 'λt.error "NYI"',
    -> TTerm:D $t -->Str{
        case-Term($t,
            VarT => -> Str $varName {
                my $varNameSrc = $varName.perl;
                "\$VarT($varNameSrc)"
            },
            AppT => -> TTerm $func, TTerm $arg {
                my $fSrc = &self($func);
                my $aSrc = &self($arg);
                "\$AppT($fSrc, $aSrc)"
            },
            LamT => -> Str $binderName, TTerm $body {
                my $binderNameSrc = $binderName.perl;
                my $bodySrc       = &self($body);
                "\$LamT($binderNameSrc, $bodySrc)"

            },
            ConstT => -> Any $val {
                my $valSrc = $val.perl;
                "\$ConstT($valSrc)"
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
        (when-AppT   (λf.λa.cons f (cons a nil))    ; (C (B (C cons) (C cons nil)))
        (when-LamT   (λv.λb.cons v (cons b nil))    ; (C (B (C cons) (C cons nil)))
        λ_.λ_.λ_.λ_.error (~ "unknown TTerm" (Term->Str t))
        ))))
ENDOFLAMBDA
    -> TTerm:D $t -->TList{
        case-Term($t,
            ConstT => $K1nil,
            VarT   => $K1nil,
            AppT => -> TTerm $func, TTerm $arg {
                $cons($func, $cons($arg, $nil))
            },
            LamT => -> Mu, TTerm $body {
                $cons($body, $nil)
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
constant $is-selfApp is export = lambdaFn(
    'selfApp?', 'not yet implemented',
    -> TTerm:D $t -->TBool{ case-Term($t,
        AppT   => -> TTerm $func, TTerm $arg {
            case-Term($func,
                VarT   => -> Str $funcName {
                    case-Term($arg,
                        VarT   => -> Str $argName { $Str-eq($funcName, $argName) },
                        ConstT => $K1false,
                        LamT   => $K2false,
                        AppT   => $K2false
                    )
                },
                ConstT => $K1false,
                LamT   => $K2false,
                AppT   => $K2false
            )
        },
        ConstT => $K1false,
        VarT   => $K1false,
        LamT   => $K2false,
    )}
);


# selfAppOf?: Str -> Term -> Bool
constant $is-selfAppOf is export = lambdaFn(
    'selfAppOf?', 'λvarName.λt.error "NYI"',
    -> Str:D $varName, TTerm $t -->TBool{
        #match-Term($t,
        #    '(LamT x (AppT (VarT x) (VarT x)))' => Str $x { $Str-eq($varName, $x) },
        #    otherwise => $false
        #)
        case-Term($t,
            AppT => -> TTerm $func, TTerm $arg {
                case-Term($func,
                    VarT => -> Str $funcName {
                        _if_( $Str-eq($varName, $funcName),
                            { case-Term($arg,
                                VarT   => -> Str $argName { $Str-eq($varName, $argName) },
                                LamT   => $K2false,
                                AppT   => $K2false,
                                ConstT => $K1false
                            ) },
                            $false
                        )
                    },
                    LamT   => $K2false,
                    AppT   => $K2false,
                    ConstT => $K1false
                )
            },
            LamT   => $K2false,
            VarT   => $K1false,
            ConstT => $K1false
        )
    }
);

# selfAppOfVar?: Term -> Term -> Bool
constant $is-selfAppOfVar is export = lambdaFn(
    'selfAppOfVar?', 'λs.λt.error "NYI"',
    -> TTerm:D $s, TTerm $t -->TBool{
        case-Term($s,
            VarT   => -> Str $sName { $is-selfAppOf($sName, $t) },
            ConstT => $K1false,
            AppT   => $K2false,
            LamT   => $K2false
        )
    }
);

constant $is-omega is export = lambdaFn(
    'ω?', 'λt.error "NYI"',
    -> TTerm:D $t -->TBool{ case-Term($t,
        LamT   => $is-selfAppOf,
        VarT   => $K1false,
        AppT   => $K2false,
        ConstT => $K1false
    ) }
);


constant $is-Omega is export = lambdaFn(
    'Ω?', 'λt.error "NYI"',
    -> TTerm:D $t -->TBool{ case-Term($t,
        AppT => -> TTerm $func, TTerm $arg {
            _if_( $is-omega($func),
                { $is-omega($arg) },
                $false
            )
        },
        LamT   => $K2false,
        VarT   => $K1false,
        ConstT => $K1false
    ) }
);


# Stream of the positive inegers: 1, 2, 3, 4, ...
my constant $pInts = $iterate(* + 1, 1);

constant $alpha-names is export = $map-lazy(-> Int $n { "α$n" }, $pInts);

constant $alpha-vars is export = $map-lazy($VarT, $alpha-names);


constant $fresh-var-for is export = {
    my $nextAlphaNr = 1;

    my role AlphaVarT[TTerm:D $for, Str:D $gist] {
        method for  { $for  }
        method gist { $gist }
    }

    my &fresh-var-error = -> $term { die "can make fresh var for another var but not for $term" };

    lambdaFn(
        'fresh-var-for', 'λfor.error "NYI"',
        -> TTerm $for -->TTerm{
            #say $nextAlphaNr;
            my $vName = 'α' ~ $nextAlphaNr;
            $nextAlphaNr++;
            my $v = $VarT($vName);
            $v ~~ TTerm or die $v.perl;
            if $for.defined { case-Term($for,
                VarT => -> Str $forName {
                    my $forStr = ($for ~~ AlphaVarT)
                        ?? $for.gist
                        !! $forName;
                    my $gistStr = $vName ~ "[/$forStr]";
                    $v does AlphaVarT[$for, $gistStr];
                },
                ConstT => -> Mu     { &fresh-var-error($for) },
                AppT   => -> Mu, Mu { &fresh-var-error($for) },
                LamT   => -> Mu, Mu { &fresh-var-error($for) }
            ) }
            $v;
        }
    );
}();



