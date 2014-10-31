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
        -> TTerm $t, TList $ss {    # TODO: add types to signature
            $_if( $is-nil($ss),
                { $None },
                { $_if( $is-ConstT($t),
                      { $None },
                      { if $t.convertToP6Bool($is-VarT($t)) {
                          my $head = $car($ss);
                          my $for  = $fst($head);
                          my $what = $snd($head);
                          my $tail = $cdr($ss);
                          if ($for.name eq $t.name) {
                              my $out = &self($what, $tail);
                              $_if( $is-Some($out),
                                  { $out },
                                  { $Some($what) }
                              );
                          } else {
                              &self($t, $tail)
                          }
                      } elsif $t.convertToP6Bool($is-AppT($t)) {
                          my $func = &self($t.func, $ss);
                          my $arg  = &self($t.arg,  $ss);
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
                          my $body = &self(
                              $t.body,
                              $filter( # kick out substs for our binder since there
                                       # won't be free occurrances of it in our body
                                  -> $x { $t.convertFromP6Bool($fst($x).name ne $t.var.name) },
                                  $ss
                              )
                          );
                          $_if( $is-Some($body),
                              { $Some($LamT($t.var, $Some2value($body))) },
                              { $None }
                          );
                      } else {
                          die "fell off type-dispatch with type " ~ $_.WHAT.perl;
                      }
                      })
                })
        }
    }
));

constant $subst is export = lambdaFn(
    'subst', 'λt.λwhat.λfor.subst-seq t (cons (Pair for what) nil)',
    -> TTerm $t, TTerm $what, TTerm $for {    # TODO: add types to signature
        $subst-seq($t, $cons($Pair($for, $what), $nil));
    }
);
