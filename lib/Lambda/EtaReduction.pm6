use v6;

use Lambda::MethodFixedPoint;


role EtaReduction[::Term, ::ConstT, ::VarT, ::AppT, ::LamT]
    #does MethodFixedPoint
{

    # η-redex? - ie of form λx.(B x) where x not free in B
    method isEtaRedex(Term:D: -->Bool) {
        given self {
            when ConstT { False }
            when VarT   { False }
            when AppT   { False }
            when LamT {
                # λx.(B x) is an η-redex if x not free in B.
                # If so, it η-contracts to just B.
                   (self.body ~~ AppT)
                && self.var.isNotFree(:in(self.body.func))
                && (self.body.arg ~~ VarT) 
                && (self.body.arg.name ~~ self.var.name)
            }
            default {
                die "fell off type-dispatch with type " ~ $_.WHAT.perl;
            }
        }
    }
 
    # either self.isEtaRedex or any child isEtaReducible
    method isEtaReducible(Term:D: --> Bool) {
        self.isEtaRedex || ?self.children.map(*.isEtaReducible).any;
    }

    # one-step η-simplification (either of self or any (one) child)
    method eta-contract() {
        given self {
            when ConstT { self }
            when VarT   { self }
            when AppT {
                return AppT.new(:func(self.func.eta-contract), :arg(self.arg))
                    if self.func.isEtaReducible;
                return AppT.new(:func(self.func), :arg(self.arg.eta-contract))
                    if self.arg.isEtaReducible;
                self;
            }
            when LamT {
                return self.body.func
                    if self.isEtaRedex;

                return LamT.new(:var(self.var), :body(self.body.eta-contract))
                    if self.body.isEtaReducible;
                self;
            }
            default {
                die "fell off type-dispatch with type " ~ $_.WHAT.perl;
            }
        }
    }
    
    method eta-reduce() {
        self.mfp(*.eta-contract);
    }

}
