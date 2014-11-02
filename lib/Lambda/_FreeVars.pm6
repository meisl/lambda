use v6;

use Lambda::FreeVars;

role FreeVars[::Term, ::ConstT, ::VarT, ::AppT, ::LamT] {

    # on VarT only
    method isFree(VarT:D: Term:D :in($t)! --> Bool:D) {
        $t.convertToP6Bool( $is-free(self, $t) );
    }

    # on VarT only
    method isFreeUnder(VarT:D: VarT:D :$binder!, Term:D :in($t)! --> Bool) {
        $t.convertToP6Bool( $is-free-under(self, $binder, $t) );
    }

    method getFreeVar(Str:D $name --> VarT) {
        given self {
            when ConstT {
                VarT;
            }
            when VarT {
                self.name eq $name ?? self !! VarT;
            }
            when AppT {
                self.func.getFreeVar($name) // .arg.getFreeVar($name);
            }
            when LamT {
                self.var.name eq $name
                    ?? VarT
                    !! self.body.getFreeVar($name);
            }
            default {
                die "unknown type " ~ self.WHAT.perl;
            }
        }
    }

    method freeVars {
        given self {
            when ConstT {
                @();
            }
            when VarT {
                 @(self,);
            }
            when AppT {
                my @left = self.func.freeVars;
                my $noneOfLeft = @left.map(*.name).none;
                return @(@left, self.arg.freeVars.grep(*.name eq $noneOfLeft));
            }
            when LamT {
                self.body.freeVars.grep(*.name ne self.var.name)
            }
            default {
                die "unknown type " ~ self.WHAT.perl;
            }
        }
    }

}
