use v6;

use Lambda::Boolean;
use Lambda::BetaReduction;

use Lambda::Conversion::Bool-conv;

use Lambda::MethodFixedPoint;


role BetaReduction[::Term, ::ConstT, ::VarT, ::AppT, ::LamT] {

    method isBetaRedex {
        convertTBool2P6Bool($is-betaRedex(self));
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
