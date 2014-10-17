use v6;


role EtaReduction[::Term, ::ConstT, ::VarT, ::AppT, ::LamT] {

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

}
