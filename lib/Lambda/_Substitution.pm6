use v6;

use Lambda::Boolean;
use Lambda::TermADT;
use Lambda::MaybeADT;
use Lambda::ListADT;
use Lambda::Substitution;


role Substitution[::Term, ::ConstT, ::VarT, ::AppT, ::LamT] is export {

    method subst(Term:D: Term:D $what, VarT:D :$for!) {   # cannot declare return type (Term) - yields really weird error msg
        my $result = $subst(self, $what, $for);
        if self.convertToP6Bool($is-None($result)) {
            return self;
        } else {
            self.convertToP6Term($Some2value($result));
        }
    }

    method subst-seq(Term:D: @substitutions) {   # cannot declare return type (Term) - yields really weird error msg
        my $result = $subst-seq(self, self.convertToListOfPairs(@substitutions));
        if self.convertToP6Bool($is-None($result)) {
            return self;
        } else {
            self.convertToP6Term($Some2value($result));
        }
    }
}
