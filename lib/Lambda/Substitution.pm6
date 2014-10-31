use v6;

use Lambda::Base;
use Lambda::Boolean;
use Lambda::MaybeADT;
use Lambda::TermADT;
use Lambda::ListADT;
use Lambda::PairADT;


constant $subst-seq is export = $Y(lambdaFn(
    'subst-seq',
q:to/ENDOFLAMBDA/,
    λself.λt.λss.
      (if (nil? ss)
          None
          (if (VarT? t)
              (let ((head (car ss))
                    (next (if (eq? (VarT->name (fst head)) (VarT->name t))  ; FIXME!
                              (snd head)
                              t)))
                (self next (cdr ss))
              )
              (if (AppT? t)
                  (let ((f (AppT->func t))
                        (a (AppT->arg  t))
                        (f´ (self f ss))
                        (a´ (self a ss))
                       )
                    (if (and (None? f') (None? a'))
                      None
                      (Some (AppT
                         (if (Some? f´) (Some->value f´) f)
                         (if (Some? a´) (Some->value a´) a)
                      ))
                    )
                  )
                  (if (LamT? t)
                      (let ((var (LamT->var t))
                            (nm  (VarT->name var))
                            (ss´ (filter    ; kick out substs for our binder
                                   (λv.not (eq? (VarT->name v) nm))
                                   ss))
                            (b´  (self (VarT->body t) ss´))
                           )
                        (if (Some? b´)
                            (Some (LamT var (Some->value b´)))
                            None
                        )
                      )
                      (error (~ "unknown Term ctor: " (Term->Str t)))
                  )
              )
          )
      )
ENDOFLAMBDA
    -> &self {
        -> $t, $ss {    # TODO: add types to signature
            if $ss.elems == 0 {
                $None;
            } else {
                if $t.convertToP6Bool($is-VarT($t)) {
                    my $head = $ss[0];
                    if ($head[0].name eq $t.name) {
                        my $out = &self($head[1], $ss[1..^*]);
                        $_if( $is-Some($out),
                            { $out },
                            { $Some($head[1]) }
                        );
                    } else {
                        &self($t, $ss[1..^*])
                    }
                } elsif $t.convertToP6Bool($is-AppT($t)) {
                    my $func = &self($t.func, $ss);
                    my $arg  = &self($t.arg, $ss);
                    $_if( $_and($is-None($func), $is-None($arg)),
                        { $None },
                        {
                            $Some($AppT(
                                $_if( $is-Some($func), { $Some2value($func) }, { $t.func } ),
                                $_if( $is-Some($arg),  { $Some2value($arg)  }, { $t.arg  } )
                            ))
                        }
                    );
                } elsif $t.convertToP6Bool($is-LamT($t)) {
                    my @ss = $ss.grep({ # kick out substs for our binder since there
                        $_[0].name ne $t.var.name  # won't be free occurrances of it in our body
                    });
                    my $body = &self($t.body, @ss);
                    $_if( $is-Some($body),
                        { $Some($LamT($t.var, $Some2value($body))) },
                        { $None }
                    );
                } else {
                    # TODO: $is-ConstT($t) -> $None;
                    die "fell off type-dispatch with type " ~ $_.WHAT.perl;
                }
            }
        }
    }
));

constant $subst is export = lambdaFn(
    'subst', 'λt.λwhat.λfor.subst-seq t (cons (Pair for what) nil)',
    -> $t, $what, $for {    # TODO: add types to signature
        $subst-seq($t, [[$for, $what]]);
    }
);
