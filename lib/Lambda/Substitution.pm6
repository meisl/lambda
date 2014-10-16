use v6;


role Substitution[::Term, ::ConstT, ::VarT, ::AppT, ::LamT] {

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

}
