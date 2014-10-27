use v6;

use Lambda::Base;
use Lambda::MaybeADT;
use Lambda::TermADT;

module Substitution;


role Substitution[::Term, ::ConstT, ::VarT, ::AppT, ::LamT] is export {

    method subst(Term:D: Term:D $what, VarT:D :$for!) {   # cannot declare return type (Term) - yields really weird error msg
        given self {
            when ConstT { self }
            when VarT {
                ($for.name ne self.name)
                    ?? self
                    !! $what
            }
            when AppT {
                my $newFnc = self.func.subst($what, :$for);
                my $newArg = self.arg.subst($what, :$for);
                (($newFnc === self.func) && ($newArg === self.arg) )
                    ?? self
                    !! AppT.new(:func($newFnc), :arg($newArg))
            }
            when LamT {
                if $for.name eq self.var.name {
                    self;
                } else {
                    my $newBody = self.body.subst($what, :$for);
                    ($newBody === self.body)
                        ?? self
                        !! LamT.new(:var(self.var), :body($newBody));
                }
            }
            default {
                die "fell off type-dispatch with type " ~ $_.WHAT.perl;
            }
        }
    }

    method subst-seq(Term:D: $substitutions) {   # cannot declare return type (Term) - yields really weird error msg
        given self {
            when ConstT { self }
            when VarT {
                if $substitutions.elems == 0 {
                    self;
                } else {
                    my $head = $substitutions[0];
                    my $next = ($head[0].name eq self.name) ?? $head[1] !! self;
                    if $substitutions.elems == 1 {
                        $next;
                    } else {
                        $next.subst-seq($substitutions[1..^*]);
                    }
                }
            }
            when AppT {
                if $substitutions.elems == 0 {
                    self;
                } else {
                    my $func = self.func.subst-seq($substitutions);
                    my $arg  = self.arg.subst-seq($substitutions);
                    if ($func === self.func) && ($arg === self.arg) {
                        self;
                    } else {
                        AppT.new(:$func, :$arg);
                    }
                }
            }
            when LamT {
                my @ss = $substitutions.grep({ # kick out substs for our binder since there
                    $_[0].name ne self.var.name  # won't be free occurrances of it in our body
                });
                if @ss.elems == 0 {
                    self;
                } else {
                    my $body = self.body.subst-seq(@ss);
                    if $body === self.body {
                        self
                    } else {
                        LamT.new(:var(self.var), :$body)
                    }
                }
            }
            default {
                die "fell off type-dispatch with type " ~ $_.WHAT.perl;
            }
        }
    }
}


constant $subst is export = lambdaFn(
    'subst',
q:to/ENDOFLAMBDA/,
    λwhere.λnew.λold.
      (if (VarT? where)
        (if (eq? (VarT->name where) (VarT->name old))
          (Some new)
          None)
        (if (AppT? where)
          (let ((f (AppT->func where))
                (a (AppT->arg  where))
                (f' (subst f new old))
                (a' (subst a new old)))
            (if (and (None? f') (None? a'))
              None
              (Some (AppT
                 (if (Some? f') (Some->value f') f)
                 (if (Some? a') (Some->value a') a)
              ))
            )
          )
          (if (LamT? where)
            (if (eq? (LamT->var (VarT->name where)) (VarT->name old))
              None  ; substitute only free occurances of ´old
              (let (b (subst (LamT->body where) new old))
                (if (None? b)
                  None
                  (Some (LamT
                          (LamT->var where)
                          (Some->value b)
                  ))
                )
              )
            )
            (error (~ "unknown Term ctor: " (Term->Str where)))
          )
        )
      )
ENDOFLAMBDA
    -> $where, $what, $for {    # TODO: add types to signature
        $where.subst($what, :$for);
    }
);
