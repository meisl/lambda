use v6;

use Lambda::MethodFixedPoint;
use Lambda::Tree;
use Lambda::_FreeVars;
use Lambda::_Substitution;
use Lambda::_EtaReduction;
use Lambda::_BetaReduction;


#use Lambda::Substitution;


class ConstT    { ... }
class VarT      { ... }
class AlphaVarT { ... }
class LamT      { ... }
class AppT      { ... }
role  Term      { ... }


role Term
    does Tree
    does MethodFixedPoint
    does FreeVars[Term, ConstT, VarT, AppT, LamT]
    does Substitution[Term, ConstT, VarT, AppT, LamT]
    does EtaReduction[Term, ConstT, VarT, AppT, LamT]
    does BetaReduction[Term, ConstT, VarT, AppT, LamT]
{
}


role LeafTerm does Term {
    method children { @() }

    method alpha-needy-terms(@vars) { @() }
}



class ConstT does LeafTerm {
    has $.value;

    submethod BUILD(:$!value!) {
    }

    method gist { ~$!value }
}


class VarT does LeafTerm {
    has Str:D $.name;

    submethod BUILD(Str:D :$!name!) {
    }
    
    my %namesToVarNodes = %();

    my $nextAlphaNr = 1;

    method fresh(VarT:T: VarT :$for --> VarT:D) {
        my $n = $for.defined
            ?? AlphaVarT.new(:name('α' ~ $nextAlphaNr), :$for)
            !! VarT.get('α' ~ $nextAlphaNr);
        $nextAlphaNr++;
        $n;
    }

    method get(VarT:T: Str:D $name --> VarT) {
        my $out = %namesToVarNodes{$name};
        unless $out.defined {
            $out = VarT.new(:$name);
            %namesToVarNodes{$name} = $out;
        }
        return $out;
    }

    method gist { ~$!name }
}

class AlphaVarT is VarT {
    has VarT:D $.for;

    method gist {
        my $out = callsame;
        $out ~ '[/' ~ $!for.gist ~ ']'
    }
}


class AppT does Term {
    has Term $.func;
    has Term $.arg; 

    submethod BUILD(Term:D :$!func!, Term:D :$!arg!) {
    }

    method children { @($!func, $!arg) }

    method gist { '(' ~ $!func.gist ~ ' ' ~ $!arg.gist ~ ')' }

    method alpha-needy-terms(@vars) {
        @($!func.alpha-needy-terms(@vars), $!arg.alpha-needy-terms(@vars))
    }

    method alpha-problematic {
        return @() unless self.isBetaRedex;
        $!arg.freeVars.grep({ $!func.var.isFreeUnder(:binder($_), :in($!func.body)) });
    }
}

class LamT does Term {
    has VarT:D $.var;
    has Term:D $.body;

    submethod BUILD(VarT:D :$!var!, Term:D :$!body!) {
    }

    method children { @($!var, $!body) }

    method gist {
        '(λ' ~ $!var.gist ~ '.' ~ $!body.gist ~ ')';
    }

    method alpha-needy-terms(@vars-to-stay-free) {
        my @wantNot = ($!var.name eq any(@vars-to-stay-free))
            ?? @( self, $!body.alpha-needy-terms(@vars-to-stay-free.grep(*.name eq $!var.name)) )
            !! $!body.alpha-needy-terms(@vars-to-stay-free);
        my @all = ($!var.name eq any(@vars-to-stay-free))
            ?? @( self, $!body.alpha-needy-terms(@vars-to-stay-free) )
            !! $!body.alpha-needy-terms(@vars-to-stay-free);
        my @want = @all.grep({$_ === @wantNot.any});
        @all;
    }

    method alpha-convert(VarT:D $newVar, VarT:D :$for --> Term) {
       !!!
    }
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