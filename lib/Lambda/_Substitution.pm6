use v6;

use Lambda::Substitution;


role Substitution[::Term, ::ConstT, ::VarT, ::AppT, ::LamT] is export {

    method subst(Term:D: Term:D $what, VarT:D :$for!) {   # cannot declare return type (Term) - yields really weird error msg
        #self.subst-seq([[$for, $what]]);
        $subst(self, $what, $for);
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
