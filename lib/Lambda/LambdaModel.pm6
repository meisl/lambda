use v6;

use Lambda::MethodFixedPoint;
use Lambda::Tree;
use Lambda::_FreeVars;
use Lambda::_Substitution;
use Lambda::_EtaReduction;
use Lambda::_BetaReduction;

use Lambda::Base;
use Lambda::TermADT;
#use Lambda::Substitution;


role ConstT    { ... }
role VarT      { ... }
role AlphaVarT { ... }
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



role ConstT does LeafTerm {
    method new(:$value!) {
        #note '>>>> ConstT.new, value=' ~ $value;
        $VarT('foo') does ConstT;
    }

    #submethod BUILD {
    #    note '>>>> ConstT.BUILD, self=' ~ self;
    #}

    method value { $VarT2name(self) }

    method gist { ~self.value }
}


role VarT does LeafTerm {

    my %namesToVarNodes = %();
    my $nextAlphaNr = 1;
    
    method new(Str:D :$name) {
        VarT.get($name);
    }

    method name { $VarT2name(self) }

    method gist { ~self.name }


    my role gist {
        has Str $.gist;
    }

    method fresh(VarT:T: VarT :$for --> VarT:D) {
        my $n = VarT.get('α' ~ $nextAlphaNr);
        $n ~~ TTerm or die $n.perl;
        if $for.defined {
            #$n does gist($n.name ~ '[/' ~ $for.gist ~ ']');
            $n does AlphaVarT(:$for);
        }
        $nextAlphaNr++;
        $n;
    }

    method get(VarT:T: Str:D $name --> VarT) {
        my $out = %namesToVarNodes{$name};
        unless $out.defined {
            $out = $VarT($name) does VarT;;
            %namesToVarNodes{$name} = $out;
        }
        return $out;
    }
}

role AlphaVarT {
    has VarT:D $.for;

    method gist {
        self.name ~ '[/' ~ $!for.gist ~ ']'
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