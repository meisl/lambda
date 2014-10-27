use v6;

use Lambda::Base;
use Lambda::MaybeADT;
use Lambda::TermADT;
use Lambda::ListADT;
use Lambda::PairADT;

module Substitution;


role Substitution[::Term, ::ConstT, ::VarT, ::AppT, ::LamT] is export {

    method subst(Term:D: Term:D $what, VarT:D :$for!) {   # cannot declare return type (Term) - yields really weird error msg
        self.subst-seq([[$for, $what]]);
    }

    method subst-seq(Term:D: $substitutions) {   # cannot declare return type (Term) - yields really weird error msg
        return self
            unless $substitutions.elems > 0;
        given self {
            when ConstT { self }
            when VarT {
                my $head = $substitutions[0];
                my $next = ($head[0].name eq self.name) ?? $head[1] !! self;
                return ($substitutions.elems == 1)
                    ?? $next
                    !! $next.subst-seq($substitutions[1..^*]);
            }
            when AppT {
                my $func = self.func.subst-seq($substitutions);
                my $arg  = self.arg.subst-seq($substitutions);
                return (($func === self.func) && ($arg === self.arg))
                    ?? self
                    !! AppT.new(:$func, :$arg);
            }
            when LamT {
                my @ss = $substitutions.grep({ # kick out substs for our binder since there
                    $_[0].name ne self.var.name  # won't be free occurrances of it in our body
                });
                my $body = self.body.subst-seq(@ss);
                return ($body === self.body)
                    ?? self
                    !! LamT.new(:var(self.var), :$body);
            }
            default {
                die "fell off type-dispatch with type " ~ $_.WHAT.perl;
            }
        }
    }
}


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
