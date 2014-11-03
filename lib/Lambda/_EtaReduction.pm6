use v6;

use Lambda::Boolean;
use Lambda::FreeVars;
use Lambda::EtaReduction;

use Lambda::Conversion::Bool-conv;


role EtaReduction[::Term, ::ConstT, ::VarT, ::AppT, ::LamT] {

    method isEtaRedex(Term:D: -->Bool) {
        convertTBool2P6Bool($is-etaRedex(self));
    }

    method isEtaReducible(Term:D: --> Bool) {
        convertTBool2P6Bool($is-etaReducible(self));
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
