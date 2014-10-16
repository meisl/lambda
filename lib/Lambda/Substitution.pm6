use v6;


role Substitution[::Term, ::ConstT, ::VarT, ::AppT, ::LamT] {

    method subst(Term:D: Term:D $what, VarT:D :$for! -->Term) {
        given self {
            when ConstT { self }
            when VarT {
                ($for.name ne self.name)
                    ?? self
                    !! $what
            }
            when AppT {
                my $newInv = self.func.subst($what, :$for);
                my $newArg = self.subst($what, :$for);
                (($newInv === self.func) && ($newArg === self.arg) )
                    ?? self
                    !! AppT.new(:func($newInv), :arg($newArg))
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
