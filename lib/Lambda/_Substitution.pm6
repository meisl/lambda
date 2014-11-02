use v6;

use Lambda::MaybeADT;
use Lambda::Substitution;

use Lambda::Conversion::ListADT-conv;


role Substitution[::Term, ::ConstT, ::VarT, ::AppT, ::LamT] is export {

    method subst(Term:D: Term:D $what, VarT:D :$for!) {   # cannot declare return type (Term) - yields really weird error msg
        my $result = $subst(self, $what, $for);
        self.convertToP6Term( $Maybe2valueWithDefault($result, self) );
    }

    method subst-seq(Term:D: @substitutions) {   # cannot declare return type (Term) - yields really weird error msg
        my $result = $subst-seq(self, convertP6ArrayToTListOfTPairs(@substitutions));
        self.convertToP6Term( $Maybe2valueWithDefault($result, self) );
    }
}
