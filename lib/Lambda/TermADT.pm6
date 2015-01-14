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

# must make the hash a constant (it's still mutable though)
# in order to have it real global
my constant %names2vars = %();

# VarT ------------------------------------------------------------------------

# VarT ctor & predicate

# VarT: Str -> (TBool -> TBool -> Str -> () -> a) -> a
constant $VarT is export = lambdaFn(
    'VarT', 'λname.λprj.prj #false #false name _',
    -> Str:D $name {
        my $out = %names2vars{$name};
        unless $out.defined {
            my $nameStr = $name.perl;
            $out = lambdaFn(
                Str, "(VarT $nameStr)",
                -> &prj { &prj($false, $false, $name, Mu) }
            ) does TTerm;
            %names2vars{$name} = $out;
#            note '>>>> ' ~ %names2vars.elems ~ ' vars now: ' ~ %names2vars;
        }
        $out;
    }
);

# VarT?: TTerm -> TBool
constant $is-VarT is export = lambdaFn(
    'VarT?', 'λt.t λtag1.λtag0.λ_.λ_._and (not tag1) (not tag0)',
    -> TTerm:D $t {
        $t(-> $tag1, $tag0, $x, $y { $_and($not($tag1), $not($tag0)) })
    }
);

# VarT projections

constant $VarT2name is export = lambdaFn(
    'VarT->name', 'λt.if (VarT? t) (t π4->3) (error (~ "cannot apply VarT->name to " (Term->Str t)))',
    -> TTerm:D $t {
        $_if( $is-VarT($t),
            -> $_ { $t($pi3o4) },
            -> $_ { die "cannot apply VarT->name to $t" }
        )
    }
);


# AppT ------------------------------------------------------------------------

# AppT ctor & predicate

constant $AppT is export = lambdaFn(
    'AppT', 'λfunc.λarg.λprj.prj #false #true func arg',
    -> TTerm:D $func, TTerm:D $arg {
        lambdaFn(
            Str, "(AppT $func $arg)",
            -> &prj { &prj($false, $true, $func, $arg) }
        ) does TTerm;
    }
);

constant $is-AppT is export = lambdaFn(
    'AppT?', 'λt.t λtag1.λtag0.λ_.λ_._and (not tag1) tag0',
    -> TTerm:D $t {
        $t(-> $tag1, $tag0, $x, $y { $_and($not($tag1), $tag0) })
    }
);

# AppT projections

constant $AppT2func is export = lambdaFn(
    'AppT->func', 'λt.if (AppT? t) (t π4->3) (error (~ "cannot apply AppT->func to " (Term->Str t)))',
    -> TTerm:D $t {
        $_if( $is-AppT($t),
            -> $_ { $t($pi3o4) },
            -> $_ { die "cannot apply AppT->func to $t" }
        )
    }
);

constant $AppT2arg is export = lambdaFn(
    'AppT->arg', 'λt.if (AppT? t) (t π4->4) (error (~ "cannot apply AppT->arg to " (Term->Str t)))',
    -> TTerm:D $t {
        $_if( $is-AppT($t),
            -> $_ { $t($pi4o4) },
            -> $_ { die "cannot apply AppT->arg to $t" }
        )
    }
);


# LamT ------------------------------------------------------------------------

# LamT ctor & predicate

constant $LamT is export = lambdaFn(
    'LamT', 'λvar.λbody.λprj.if (VarT? var) (prj #true #false var body) (error (~ "first arg to LamT ctor must be a VarT - got instead " (->Str var)))',
    -> TTerm:D $var, TTerm:D $body {
        $_if( $is-VarT($var),
            -> $_ { lambdaFn(
                        Str, "(LamT $var $body)",
                        -> &prj { &prj($true, $false, $var, $body) }
                    ) does TTerm;
            },
            -> $_ { die "first arg to LamT ctor must be a VarT - got instead $var" }
        )
    }
);

constant $is-LamT is export = lambdaFn(
    'LamT?', 'λt.t λtag1.λtag0.λ_.λ_._and tag1 (not tag0)',
    -> TTerm:D $t {
        $t(-> $tag1, $tag0, $x, $y { $_and($tag1, $not($tag0)) })
    }
);

# LamT projections

constant $LamT2var is export = lambdaFn(
    'LamT->var', 'λt.if (LamT? t) (t π4->3) (error (~ "cannot apply LamT->var to " (Term->Str t)))',
    -> TTerm:D $t {
        $_if( $is-LamT($t),
            -> $_ { $t($pi3o4) },
            -> $_ { die "cannot apply LamT->var to $t" }
        )
    }
);

constant $LamT2body is export = lambdaFn(
    'LamT->body', 'λt.if (LamT? t) (t π4->4) (error (~ "cannot apply LamT->body to " (Term->Str t)))',
    -> TTerm:D $t {
        $_if( $is-LamT($t),
            -> $_ { $t($pi4o4) },
            -> $_ { die "cannot apply LamT->body to $t" }
        )
    }
);


# ConstT ----------------------------------------------------------------------

# ConstT ctor & predicate

constant $ConstT is export = lambdaFn(
    'ConstT', 'value.λprj.prj #true #true value _',
    -> $value {
        my $valueStr = $value.perl;
        lambdaFn(
            Str, "(ConstT $valueStr)",
            -> &prj { &prj($true, $true, $value, Mu) }
        ) does TTerm;
    }
);

constant $is-ConstT is export = lambdaFn(
    'ConstT?', 'λt.t λtag1.λtag0.λ_.λ_.(_and tag1 tag0)',
    -> TTerm:D $t {
        $t(-> $tag1, $tag0, $x, $y { $_and($tag1, $tag0) })
    }
);

# ConstT projections

constant $ConstT2value is export = lambdaFn(
    'ConstT->value', 'λt.if (ConstT? t) (t π4->3) (error (~ "cannot apply ConstT->value to " (Term->Str t)))',
    -> TTerm:D $t {
        $_if( $is-ConstT($t),
            -> $_ { $t($pi3o4) },
            -> $_ { die "cannot apply ConstT->value to $t" }
        )
    }
);


# ->Str -----------------------------------------------------------------------

constant $Term2Str is export = lambdaFn(
    'Term->Str', 'λt.(error "NYI")',
    -> TTerm:D $t { $t.Str }
);


# pattern-matching ------------------------------------------------------------

constant $given-Term is export = lambdaFn(
    'given-Term', 'λterm.λcases.term cases',
    -> TTerm:D $t, &cases { $t(&cases) }
);

constant $make-when_2_2 = lambdaFn(
    'make-when-2-2', 
q:to/ENDOFLAMBDA/,
    λexpTag1.λexpTag0.λactTag1.λactTag0.λthenFn.λotherwise.
        if (_and (_eqv expTag1 actTag1) (_eqv expTag0 actTag0))
            thenFn
            (otherwise actTag1 actTag0)
ENDOFLAMBDA
    -> Str:D $ctorName, TBool:D $expTag1, TBool:D $expTag0 {
        my $nameStr   = 'when-' ~ $ctorName;
        my $condStr   = "(_and (_eqv $expTag1 actTag1) (_eqv $expTag0 actTag0))";
        my $lambdaStr = "λtag1.λtag0.λthenFn.λotherwise.if $condStr thenFn (otherwise tag1 tag0)";
        lambdaFn(
            $nameStr, $lambdaStr,
            -> &thenFn, &otherwise, TBool:D $actTag1, TBool:D $actTag0 {
                $_if( $_and($_eqv($expTag1, $actTag1), $_eqv($expTag0, $actTag0)),
                    -> $_ { &thenFn },
                    -> $_ { curry(&otherwise)($actTag1, $actTag0) }
                )
            }
        )
    }
);

constant $when-VarT     is export = $make-when_2_2('VarT',      $false,     $false);
constant $when-AppT     is export = $make-when_2_2('AppT',      $false,     $true );
constant $when-LamT     is export = $make-when_2_2('LamT',      $true,      $false);
constant $when-ConstT   is export = $make-when_2_2('ConstT',    $true,      $true );


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
               (~ "(LAMBDA" (~ vSrc (~ DOT (~ bSrc ")"))))    ; TODO: put literal lambda and dot here
            )
        )
        λ_.λ_.λ_.λ_.error (~ "unknown TTerm" (Term->Str t))
        ))))
ENDOFLAMBDA
    -> &self {
        -> TTerm:D $t -->Str{
            $given-Term($t,
                $when-ConstT(-> $val, Mu { $val.perl},    #   $B($pi1o2, *.perl),
                $when-VarT($pi1o2,
                $when-AppT(-> $func, $arg {
                    my $fSrc = &self($func);
                    my $aSrc = &self($arg);
                    "($fSrc $aSrc)"
                },
                $when-LamT(-> $var, $body {
                    my $vSrc = &self($var);
                    my $bSrc = &self($body);
                    "(λ$vSrc.$bSrc)"

                },
                -> $tag1, $tag0, $field0, $field1 { die "fell off type-dispatch with type " ~ $t.WHAT.perl }
            )))))
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
        $given-Term($t,
            $when-ConstT(-> $n, Mu { $nil },
            $when-VarT(  -> $n, Mu { $nil },
            $when-AppT(  -> $f, $a { $cons($f, $cons($a, $nil)) },
            $when-LamT(  -> $v, $b { $cons($v, $cons($b, $nil)) },
            -> $tag1, $tag0, $field0, $field1 { die "fell off type-dispatch with type " ~ $t.WHAT.perl }
        )))))
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


constant $is-selfApp is export = lambdaFn(
    'selfApp?',
q:to/ENDOFLAMBDA/,
#    λt.given t
#        (when (AppT (VarT fName) (VarT aName)) (eq? fName aName)
#        (λ_.λ_.λ_.λ_.false)
#    )
    λt.given-Term t
        (when-AppT (λf.λa.
            given-Term f
                (when-VarT (λfName.λ_.
                    given-Term a
                        (when-VarT (λaName.λ_.
                            eq? fName aName
                        )
                        λ_.λ_.λ_.λ_.#false
                    )
                )
                λ_.λ_.λ_.λ_.#false
            )
        )
        λ_.λ_.λ_.λ_.#false
        )
ENDOFLAMBDA
    -> TTerm:D $t -->TBool{
        #say "inside is-selfApp";
        my $otherwise = -> $tag1, $tag0, $field0, $field1 {
            #say "done is-selfApp";
            $false
        }
        $given-Term($t,
            $when-AppT(-> $f, $a {
                $given-Term($f,
                    $when-VarT(-> $fName, Mu {
                        $given-Term($a,
                            $when-VarT(-> $aName, Mu {
                                #say "done is-selfApp";
                                convertP6Bool2TBool($fName eq $aName)    # TODO: dispense with convertP6Bool2TBool
                            },
                            $otherwise
                            )
                        )
                    },
                    $otherwise
                    )
                )
            },
            $otherwise
            )
        )
    }
);


constant $is-omega is export = lambdaFn(
    'ω?',
q:to/ENDOFLAMBDA/,
    λt.given-Term t
        (when-LamT (λv.λb.
            _if (selfApp? b)
                (λ_.eq? (VarT->name (AppT->func b)) (VarT->name v))
                (K #false)
            
        )
        λ_.λ_.λ_.λ_.#false
        )
ENDOFLAMBDA
    -> TTerm:D $t -->TBool{
        $given-Term($t,
            $when-LamT(-> TTerm $v, TTerm $b {
                $_if( $is-selfApp($b),
                    -> $_ { convertP6Bool2TBool($VarT2name($AppT2func($b)) eq $VarT2name($v)) },    # TODO: dispense with convertP6Bool2TBool
                    -> $_ { $false }
                )
        
            },
            -> $tag1, $tag0, $field0, $field1 { $false }
            )
        )
    }
);


constant $is-Omega is export = lambdaFn(
    'Ω?',
q:to/ENDOFLAMBDA/,
    λt.given-Term t
        (when-AppT (λf.λa.
           (_and (ω? f) (ω? a))
        )
        λ_.λ_.λ_.λ_.#false
        )
ENDOFLAMBDA
    -> TTerm:D $t -->TBool{
        $given-Term($t,
            $when-AppT(-> TTerm $f, TTerm $a {
                $_and($is-omega($f), $is-omega($a))
            },
            -> $tag1, $tag0, $field0, $field1 { $false }
            )
        )
    }
);



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
                $is-VarT($for) or die "can make fresh var for another var but not for $for";
                $v does AlphaVarT(:$for);
            }
            $nextAlphaNr++;
            $v;
        }
    );
}();
