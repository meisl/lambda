use v6;

use Lambda::Boolean;
use Lambda::TermADT;
use Lambda::MaybeADT;
use Lambda::ListADT;
use Lambda::Substitution;


role Substitution[::Term, ::ConstT, ::VarT, ::AppT, ::LamT] is export {

    method subst(Term:D: Term:D $what, VarT:D :$for!) {   # cannot declare return type (Term) - yields really weird error msg
        my $result = $subst(self, $what, $for);
        self.convertToP6Term( $Maybe2valueWithDefault($result, self) );
    }

    method subst-seq(Term:D: @substitutions) {   # cannot declare return type (Term) - yields really weird error msg
        my $result = $subst-seq(self, self.convertToListOfPairs(@substitutions));
        self.convertToP6Term( $Maybe2valueWithDefault($result, self) );
    }
}
