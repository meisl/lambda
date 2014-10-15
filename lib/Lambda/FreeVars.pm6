use v6;


role FreeVars[::Term, ::ConstT, ::VarT, ::AppT, ::LamT] {

    method _ {
        given self {
            when ConstT {  }
            when VarT   {  }
            when AppT   {  }
            when LamT   {  }
            default {
                die "unknown type " ~ .WHAT.perl;
            }
        }
    }

    # on VarT only
    method isFree(VarT:D: Term:D :in($t)! --> Bool:D) {
        given $t {
            when ConstT { False }
            when VarT   { self.name eq $t.name }
            when AppT   { self.isFree(:in($t.func)) || self.isFree(:in($t.arg)) }
            when LamT   { ($t.var.name ne self.name) && self.isFree(:in($t.body)) }
            default {
                die "unknown type " ~ .WHAT.perl;
            }
        }
    }

    # on VarT only
    method isNotFree(VarT:D: Term:D :$in! --> Bool:D) {
        !self.isFree(:$in);
    }

    # on VarT only
    method isFreeUnder(VarT:D: VarT:D :$binder!, Term:D :in($t)! --> Bool) {
        given $t {
            when ConstT { False }
            when VarT   { False }
            when AppT {
                   self.isFreeUnder(:$binder, :in($t.func))
                || self.isFreeUnder(:$binder, :in($t.arg))
            }
            when LamT {
                ($t.var.name ne self.name) # if the λ binds us then we're not free anywhere in the λ's body
                && ($binder.name eq $t.var.name)    # or else, if the binder is the λ's var then...
                    ?? self.isFree(:in($t.body))                # we're free if we're free in the λ's body
                    !! self.isFreeUnder(:$binder, :in($t.body)) # otherwise it depends on the λ's body
            }
            default {
                die "unknown type " ~ .WHAT.perl;
            }
        }
    }

    method getFreeVar(Str:D $name --> VarT) {
        given self {
            when ConstT {
                VarT;
            }
            when VarT {
                .name eq $name ?? self !! VarT;
            }
            when AppT {
                .func.getFreeVar($name) // .arg.getFreeVar($name);
            }
            when LamT {
                .var.name eq $name
                    ?? VarT
                    !! .body.getFreeVar($name);
            }
            default {
                die "unknown type " ~ .WHAT.perl;
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
                my @left = .func.freeVars;
                my $noneOfLeft = @left.map(*.name).none;
                return @(@left, .arg.freeVars.grep(*.name eq $noneOfLeft));
            }
            when LamT {
                .body.freeVars.grep(*.name ne .var.name)
            }
            default {
                die "unknown type " ~ .WHAT.perl;
            }
        }
    }

}
