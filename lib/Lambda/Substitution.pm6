use v6;

use Lambda::Base;
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
                    (next (if (eq? (VarT->name (fst head)) (VarT->name t))
                              (Some (snd head))
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
                        (if (None? b´)
                            None
                            (Some (LamT var b´))
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
            die "NYI";  #$t.subst-seq($ss);
        }
    }
));

constant $subst is export = lambdaFn(
    'subst', 'λt.λwhat.λfor.subst-seq t (cons (Pair for what) nil)',
    -> $t, $what, $for {    # TODO: add types to signature
        $t.$subst-seq([[$for, $what]]);
    }
);
