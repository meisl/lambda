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

    method hasFreeVar(VarT:D $var --> Bool:D) {
        given self {
            when ConstT { False }
            when VarT   { .name eq $var.name }
            when AppT   { .func.hasFreeVar($var) || .arg.hasFreeVar($var) }
            when LamT   { (.var.name ne $var.name) && .body.hasFreeVar($var) }
            default {
                die "unknown type " ~ .WHAT.perl;
            }
        }
    }

    method isFreeUnderBinder(VarT:D $var, VarT:D :$binder --> Bool) {
        given self {
            when ConstT { False }
            when VarT   { False }
            when AppT {
                .func.isFreeUnderBinder($var, :$binder)
                || .arg.isFreeUnderBinder($var, :$binder)
            }
            when LamT {
                ($var.name ne .var.name) # if we bind it then it's not free anywhere in our body
                && ($binder.name eq .var.name) # or else, if the binder is ours then...
                    ?? .body.hasFreeVar($var)  # it's free if it's free in the body
                    !! .body.isFreeUnderBinder($var, :$binder) # otherwise it depends on body
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

}
