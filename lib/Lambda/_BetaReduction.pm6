use v6;

use Lambda::Boolean;
use Lambda::MaybeADT;
use Lambda::BetaReduction;

use Lambda::Conversion::Bool-conv;

use Lambda::MethodFixedPoint;


role BetaReduction[::Term, ::ConstT, ::VarT, ::AppT, ::LamT] {

    method isBetaRedex {
        convertTBool2P6Bool($is-betaRedex(self));
    }

    method isBetaReducible {
        convertTBool2P6Bool($is-betaReducible(self));
    }

    method beta-contract {
        self.convertToP6Term( $Maybe2valueWithDefault($betaContract(self), self) );
    }

    method beta-reduce() {
        self.mfp(*.beta-contract);
    }

}
