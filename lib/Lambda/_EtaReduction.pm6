use v6;

use Lambda::Boolean;
use Lambda::MaybeADT;
use Lambda::EtaReduction;

use Lambda::Conversion::Bool-conv;


role EtaReduction[::Term, ::ConstT, ::VarT, ::AppT, ::LamT] {

    method isEtaRedex(Term:D: -->Bool) {
        convertTBool2P6Bool($is-etaRedex(self));
    }

    method isEtaReducible(Term:D: --> Bool) {
        convertTBool2P6Bool($is-etaReducible(self));
    }

    method eta-contract() {
        self.convertToP6Term( $Maybe2valueWithDefault($etaContract(self), self) );
    }
    
    method eta-reduce() {
        self.mfp(*.eta-contract);
    }

}
