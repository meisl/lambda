use v6;

use Lambda::MaybeADT;
use Lambda::FreeVars;

use Lambda::Conversion::ListADT-conv;
use Lambda::Conversion::Bool-conv;


role FreeVars[::Term, ::ConstT, ::VarT, ::AppT, ::LamT] {

    # on VarT only
    method isFree(VarT:D: Term:D :in($t)! --> Bool:D) {
        convertTBool2P6Bool( $is-free(self, $t) );
    }

    # on VarT only
    method isFreeUnder(VarT:D: VarT:D :$binder!, Term:D :in($t)! --> Bool) {
        convertTBool2P6Bool( $is-free-under(self, $binder, $t) );
    }

    method getFreeVar(Str:D $name --> VarT) {
        $Maybe2valueWithDefault($free-var($name, self), VarT);
    }

    method freeVars {
        convertTList2P6Array($free-vars(self));
    }

}
