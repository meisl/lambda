use v6;

use Lambda::Base;
use Lambda::Boolean;
use Lambda::PairADT;
use Lambda::MaybeADT;
use Lambda::ListADT;
use Lambda::TermADT;

use Lambda::Substitution;
use Lambda::FreeVars;
use Lambda::EtaReduction;
use Lambda::BetaReduction;

use Lambda::Conversion::ListADT-conv;
use Lambda::Conversion::Bool-conv;


role ConstT { ... }
role VarT   { ... }
role AppT   { ... }
role LamT   { ... }

role Term   { ... }; # Do NOT remove, otherwise we'll get "===SORRY!=== Cannot invoke null object" (?!)


sub convertToP6Term(TTerm:D $t) is export {
    return $t
        if $t ~~ Term;
    if convertTBool2P6Bool($is-VarT($t)) {
        return $t but VarT;   # TODO: what about VarT.get in this case?
    } elsif convertTBool2P6Bool($is-ConstT($t)) {
        return $t but ConstT;
    } elsif convertTBool2P6Bool($is-AppT($t)) {
        my $func = $AppT2func($t);
        my $arg  = $AppT2arg($t);
        if ($func ~~ Term) && ($arg ~~ Term) {
            return $t but AppT;
        }
        my $newFunc = convertToP6Term($func);
        my $newArg  = convertToP6Term($arg);
        return AppT.new(:func($newFunc), :arg($newArg));
    } elsif convertTBool2P6Bool($is-LamT($t)) {
        my $var  = $LamT2var($t);
        my $body = $LamT2body($t);
        if ($var ~~ Term) && ($body ~~ Term) {
            return $t but LamT;
        }
        my $newVar  = convertToP6Term($var);
        my $newBody = convertToP6Term($body);
        return LamT.new(:var($newVar), :body($newBody));
    } else {
        die "cannot convert $t";
    }
}

role Term {

    method convertToP6Term(TTerm:D $t) { convertToP6Term($t) }

    # Substitution ------------------------------------------------------------

    method subst(Term:D: Term:D $what, VarT:D :$for!) {   # cannot declare return type (Term) - yields really weird error msg
        my $result = $subst(self, $what, $for);
        self.convertToP6Term( $Maybe2valueWithDefault($result, self) );
    }

    method subst-seq(Term:D: @substitutions) {   # cannot declare return type (Term) - yields really weird error msg
        my $result = $subst-seq(self, convertP6ArrayToTListOfTPairs(@substitutions));
        self.convertToP6Term( $Maybe2valueWithDefault($result, self) );
    }

    # FreeVars ----------------------------------------------------------------

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

    # EtaReduction ------------------------------------------------------------

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
        self.convertToP6Term( $Maybe2valueWithDefault($etaReduce(self), self) );
    }

    # BetaReduction -----------------------------------------------------------

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
        self.convertToP6Term( $Maybe2valueWithDefault($betaReduce(self), self) );
    }

}



role ConstT does Term {
    method value { $ConstT2value(self) }

    method new(:$value!) {
        #note '>>>> ConstT.new, value=' ~ $value;
        $ConstT($value) does ConstT;
    }
}


role VarT does Term {
    method name { $VarT2name(self) }
    
    method new(Str:D :$name) {
        $VarT($name);
    }

    my $nextAlphaNr = 1;

    my role AlphaVarT {
        has TTerm:D $.for;

        method gist {
            my $forStr = ($!for ~~ AlphaVarT)
                ?? $!for.gist
                !! $VarT2name($!for);
            self.name ~ "[/$forStr]";
        }
    }

    method fresh(VarT:T: TTerm :$for --> VarT:D) {
        my $v = $VarT('α' ~ $nextAlphaNr) does VarT;
        $v ~~ TTerm or die $v.perl;
        if $for.defined {
            $is-VarT($for) or die "can make fresh var for another var but not for $for";
            $v does AlphaVarT(:$for);
        }
        $nextAlphaNr++;
        $v;
    }
}


role AppT does Term {
    method func { $AppT2func(self) }
    method arg  { $AppT2arg(self)  }

    method new(Term:D :$func!, Term:D :$arg!) {
        $AppT($func, $arg) does AppT;
    }

    method alpha-needy-terms(@vars) {
        @(self.func.alpha-needy-terms(@vars), self.arg.alpha-needy-terms(@vars))
    }

    method alpha-problematic {
        return @() unless self.isBetaRedex;
        self.arg.freeVars.grep({ self.func.var.isFreeUnder(:binder($_), :in(self.func.body)) });
    }
}

role LamT does Term {
    method var  { $LamT2var(self) }
    method body { $LamT2body(self) }

    method new(VarT:D :$var!, Term:D :$body!) {
        $LamT($var, $body) does LamT;
    }

    method alpha-needy-terms(@vars-to-stay-free) {
        my @wantNot = (self.var.name eq any(@vars-to-stay-free))
            ?? @( self, self.body.alpha-needy-terms(@vars-to-stay-free.grep(*.name eq self.var.name)) )
            !! self.body.alpha-needy-terms(@vars-to-stay-free);
        my @all = (self.var.name eq any(@vars-to-stay-free))
            ?? @( self, self.body.alpha-needy-terms(@vars-to-stay-free) )
            !! self.body.alpha-needy-terms(@vars-to-stay-free);
        my @want = @all.grep({$_ === @wantNot.any});
        @all;
    }

    #method alpha-convert(VarT:D $newVar, VarT:D :$for --> Term) {
    #   !!!
    #}
}


class DefNode does Term {
    has VarT:D $.symbol;
    has Term:D $.term;

    submethod BUILD(:$!symbol!, :$!term!) {
    }

    method gist {
        "(δ $!symbol " ~ $!term.gist ~ ')';
    }

}

#say $lam.alpha-convert($z, :for($lam.var));