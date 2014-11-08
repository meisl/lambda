use v6;

use Lambda::Base;
use Lambda::Boolean;
use Lambda::ListADT;

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
            { $t($pi3o4) },
            { die "cannot apply VarT->name to $t" }
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
            { $t($pi3o4) },
            { die "cannot apply AppT->func to $t" }
        )
    }
);

constant $AppT2arg is export = lambdaFn(
    'AppT->arg', 'λt.if (AppT? t) (t π4->4) (error (~ "cannot apply AppT->arg to " (Term->Str t)))',
    -> TTerm:D $t {
        $_if( $is-AppT($t),
            { $t($pi4o4) },
            { die "cannot apply AppT->arg to $t" }
        )
    }
);


# LamT ------------------------------------------------------------------------

# LamT ctor & predicate

constant $LamT is export = lambdaFn(
    'LamT', 'λvar.λbody.λprj.if (VarT? var) (prj #true #false var body) (error (~ "first arg to LamT ctor must be a VarT - got instead " (->Str var)))',
    -> TTerm:D $var, TTerm:D $body {
        $_if( $is-VarT($var),
            { lambdaFn(
                Str, "(LamT $var $body)",
                -> &prj { &prj($true, $false, $var, $body) }
              ) does TTerm;
            },
            { die "first arg to LamT ctor must be a VarT - got instead $var" }
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
            { $t($pi3o4) },
            { die "cannot apply LamT->var to $t" }
        )
    }
);

constant $LamT2body is export = lambdaFn(
    'LamT->body', 'λt.if (LamT? t) (t π4->4) (error (~ "cannot apply LamT->body to " (Term->Str t)))',
    -> TTerm:D $t {
        $_if( $is-LamT($t),
            { $t($pi4o4) },
            { die "cannot apply LamT->body to $t" }
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
            { $t($pi3o4) },
            { die "cannot apply ConstT->value to $t" }
        )
    }
);


# ->Str -----------------------------------------------------------------------

constant $Term2Str is export = lambdaFn(
    'Term->Str', 'λt.(error "NYI")',
    -> TTerm:D $t { $t.Str }
);


# functions on Term -----------------------------------------------------------

constant $Term2source is export = $Y(lambdaFn(
    'Term->source', 
q:to/ENDOFLAMBDA/,
    λself.λt.case t ; TODO: case -> cascaded if
        (((ConstT val)    (->Str val))
         ((VarT name)     name)
         ((AppT func arg)
             (let ((fSrc (self func))
                   (aSrc (self arg))
                  )
                (~ "(" (~ fSrc (~ aSrc ")")))
             )
         )
         ((LamT v body)
             (let ((vSrc (self v))
                   (bSrc (self body))
                  )
                (~ "(LAMBDA" (~ vSrc (~ DOT (~ bSrc ")"))))    ; TODO: put literal lambda and dot here
            )
         )
        )
       (error (~ "unknown TTerm" (Term->Str t)))
ENDOFLAMBDA
    -> &self {
        -> TTerm:D $t {
            $_if( $is-VarT($t),
                { $VarT2name($t) },
                { $_if( $is-ConstT($t),
                      { $ConstT2value($t).perl },
                      { $_if( $is-AppT($t),
                            { my $fSrc = &self($AppT2func($t));
                              my $aSrc = &self($AppT2arg($t));
                              "($fSrc $aSrc)";
                            },
                            { $_if( $is-LamT($t),
                                  { my $vSrc = &self($LamT2var($t));
                                    my $bSrc = &self($LamT2body($t));
                                    "(λ$vSrc.$bSrc)",
                                  },
                                  { die "fell off type-dispatch with type " ~ $t.WHAT.perl }
                              )
                            }
                        )
                      }
                  )
                }
            )
        }
    }
));


constant $Term2children is export = lambdaFn(
    'Term->children', 
q:to/ENDOFLAMBDA/,
    λt.case t ; TODO: case -> cascaded if
        (((ConstT val)    nil)
         ((VarT name)     nil)
         ((AppT f a)      (cons f (cons a nil)))
         ((LamT v b)      (cons v (cons b nil)))
        )
        (error (~ "unknown TTerm" (Term->Str t)))
ENDOFLAMBDA
    -> TTerm:D $t {
        $_if( $_or($is-VarT($t), $is-ConstT($t)),
            { $nil },
            { $_if( $is-AppT($t),
                  { $cons($AppT2func($t), $cons($AppT2arg($t), $nil)) },
                  { $_if( $is-LamT($t),
                        { $cons($LamT2var($t), $cons($LamT2body($t), $nil)) },
                        { die "fell off type-dispatch with type " ~ $t.WHAT.perl }
                    )
                  }
              )
            }
        )
    }
);


constant $is-selfApp is export = lambdaFn(
    'selfApp?',
q:to/ENDOFLAMBDA/,
    λt._if (AppT? t)
           (let ((f (AppT->func t))
                 (a (AppT->arg t))
                )
             (_if (_and (VarT f) (VarT a))
                  (λ_.eq? (VarT->name f) (VarT->name a))
                  (K #false)
             )
           )
           (K #false)
ENDOFLAMBDA
    -> TTerm:D $t {
        $_if( $is-AppT($t),
            { my $f = $AppT2func($t);
              my $a = $AppT2arg($t);
              $_if( $_and($is-VarT($f), $is-VarT($a)),
                  { convertP6Bool2TBool($VarT2name($f) eq $VarT2name($a)) },    # TODO: dispense with convertP6Bool2TBool
                  { $false }
              )
            },
            { $false }
        )
    }
);


constant $is-omega is export = lambdaFn(
    'ω?',
q:to/ENDOFLAMBDA/,
    λt._if (LamT? t)
           (let ((v (LamT->var  t))
                 (b (LamT->body t))
                )
             (_if (selfApp? b)
                  (λ_.eq? (VarT->name (AppT->func b)) (VarT->name v))
                  (K #false)
             )
           )
           (K #false)
ENDOFLAMBDA
    -> TTerm:D $t {
        $_if( $is-LamT($t),
            { my $v = $LamT2var($t);
              my $b = $LamT2body($t);
              $_if( $is-selfApp($b),
                  { convertP6Bool2TBool($VarT2name($AppT2func($b)) eq $VarT2name($v)) },    # TODO: dispense with convertP6Bool2TBool
                  { $false }
              )
            },
            { $false }
        )
    }
);


constant $is-Omega is export = lambdaFn(
    'Ω?',
q:to/ENDOFLAMBDA/,
    λt._if (AppT? t)
           (_and (ω? (AppT->func t)) (ω? (AppT->arg t)))
           (K #false)
ENDOFLAMBDA
    -> TTerm:D $t {
        $_if( $is-AppT($t),
            { $_and($is-omega($AppT2func($t)), $is-omega($AppT2arg($t))) },
            { $false }
        )
    }
);


constant $Term2size is export = $Y(lambdaFn(
    'Term->size', 'λself.λt.(foldl (λacc.λchild.(+ acc (self child))) 1 (Term->children t))',
    -> &self {
        -> TTerm:D $t {
            $foldl(-> $acc, $child { $acc + &self($child) }, 1, $Term2children($t));
        }
    }
));