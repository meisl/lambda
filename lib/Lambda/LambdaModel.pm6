use v6;

use Lambda::MethodFixedPoint;
use Lambda::Tree;
use Lambda::_FreeVars;
use Lambda::_Substitution;
use Lambda::_EtaReduction;
use Lambda::_BetaReduction;

use Lambda::Base;
use Lambda::Boolean;
use Lambda::PairADT;
use Lambda::MaybeADT;
use Lambda::ListADT;
use Lambda::TermADT;
#use Lambda::Substitution;

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
        return $t does VarT;   # TODO: what about VarT.get in this case?
    } elsif convertTBool2P6Bool($is-ConstT($t)) {
        return $t does ConstT;
    } elsif convertTBool2P6Bool($is-AppT($t)) {
        my $func = $AppT2func($t);
        my $arg  = $AppT2arg($t);
        if ($func ~~ Term) && ($arg ~~ Term) {
            return $t does AppT;
        }
        my $newFunc = convertToP6Term($func);
        my $newArg  = convertToP6Term($arg);
        return AppT.new(:func($newFunc), :arg($newArg));
    } elsif convertTBool2P6Bool($is-LamT($t)) {
        my $var  = $LamT2var($t);
        my $body = $LamT2body($t);
        if ($var ~~ Term) && ($body ~~ Term) {
            return $t does LamT;
        }
        my $newVar  = convertToP6Term($var);
        my $newBody = convertToP6Term($body);
        return LamT.new(:var($newVar), :body($newBody));
    } else {
        die "cannot convert $t";
    }
}

role Term
    does Tree
    does MethodFixedPoint
    does FreeVars[Term, ConstT, VarT, AppT, LamT]
    does Substitution[Term, ConstT, VarT, AppT, LamT]
    does EtaReduction[Term, ConstT, VarT, AppT, LamT]
    does BetaReduction[Term, ConstT, VarT, AppT, LamT]
{

    method convertToP6Term(TTerm:D $t) { convertToP6Term($t) }
}


role LeafTerm does Term {
    method children { @() }

    method alpha-needy-terms(@vars) { @() }
}



role ConstT does LeafTerm {
    method value { $ConstT2value(self) }

    method new(:$value!) {
        #note '>>>> ConstT.new, value=' ~ $value;
        $ConstT($value) does ConstT;
    }

    method gist { self.value.perl }
}


role VarT does LeafTerm {
    method name { $VarT2name(self) }
    
    method new(Str:D :$name) {
        VarT.get($name);
    }

    method gist { ~self.name }


    my %namesToVarNodes = %();
    my $nextAlphaNr = 1;

    my role AlphaVarT {
        has VarT:D $.for;

        method gist {
            self.name ~ '[/' ~ $!for.gist ~ ']'
        }
    }

    method fresh(VarT:T: VarT :$for --> VarT:D) {
        my $n = VarT.get('α' ~ $nextAlphaNr);
        $n ~~ TTerm or die $n.perl;
        if $for.defined {
            $n does AlphaVarT(:$for);
        }
        $nextAlphaNr++;
        $n;
    }

    method get(VarT:T: Str:D $name --> VarT) {
        my $out = %namesToVarNodes{$name};
        unless $out.defined {
            $out = $VarT($name) does VarT;
            %namesToVarNodes{$name} = $out;
        }
        return $out;
    }
}


role AppT does Term {
    method func { $AppT2func(self) }
    method arg  { $AppT2arg(self)  }

    method new(Term:D :$func!, Term:D :$arg!) {
        $AppT($func, $arg) does AppT;
    }

    method children { @(self.func, self.arg) }

    method gist { '(' ~ self.func.gist ~ ' ' ~ self.arg.gist ~ ')' }

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

    method children { @(self.var, self.body) }

    method gist {
        '(λ' ~ self.var.gist ~ '.' ~ self.body.gist ~ ')';
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

    method children { @($!symbol, $!term) }

    method gist {
        "(δ $!symbol " ~ $!term.gist ~ ')';
    }

}

#say $lam.alpha-convert($z, :for($lam.var));