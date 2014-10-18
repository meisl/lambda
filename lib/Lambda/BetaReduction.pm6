use v6;

use Lambda::MethodFixedPoint;


role BetaReduction[::Term, ::ConstT, ::VarT, ::AppT, ::LamT]
    #does MethodFixedPoint
{

     # β-redex? - ie of form ((λx.B) z)
    method isBetaRedex {
        given self {
            when ConstT { False }
            when VarT   { False }
            when LamT   { False }
            when AppT {
                # (P Q) is a β-redex if P is of form (λx.B).
                # If so, it β-contracts to [P/x] B, ie P substituted for x
                # in the λ's body but beware: any free var in P
                # must NOT be accidentally captured by a binding in B.
                # If that would be the case, we need to α-convert before.
                (self.func ~~ LamT)
            }
            default {
                die "fell off type-dispatch with type " ~ $_.WHAT.perl;
            }
        }
    }

    # either self.isBetaRedex or any child isBetaReducible
    method isBetaReducible {
        self.isBetaRedex
        || ?self.children.map(*.isBetaReducible).any;
    }

    # one-step β-simplification (either of self or any (one) child)
    method beta-contract {
        given self {
            when ConstT { self }
            when VarT   { self }
            when LamT {
                return self
                    unless self.body.isBetaReducible;
                LamT.new(:var(self.var), :body(self.body.beta-contract));
            }
            when AppT {
                return self
                    unless self.isBetaReducible;
                if (self.isBetaRedex) {
                    my $out;
                    my $for = self.func.var;
                    my $in  = self.func.body;
                    my $what = self.arg;
                    my @toKeepFree = $what.freeVars.grep(*.name ne $for.name);
                    my @alpha-problematic = @toKeepFree.grep({$for.isFreeUnder(:binder($_), :$in)});
                    if @alpha-problematic.elems > 0 {
                        die "Cannot alpha-convert for " ~ @alpha-problematic ~ " yet.";
                    } else {
                        $out = $in.subst($what, :$for);
                    }
                    return $out.Str eq self.Str ?? self !! $out;
                } elsif self.func.isBetaReducible {
                    return AppT.new(:func(self.func.beta-contract), :arg(self.arg));
                } elsif self.arg.isBetaReducible {
                    return AppT.new(:func(self.func), :arg(self.arg.beta-contract));
                }
            }
            default {
                die "fell off type-dispatch with type " ~ $_.WHAT.perl;
            }
        }
    }

    
    method beta-reduce() {
        self.mfp(*.beta-contract);
    }

}
