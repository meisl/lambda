use v6;

use Lambda::MethodFixedPoint;
use Lambda::Tree;
use Lambda::FreeVars;
use Lambda::Substitution;
use Lambda::EtaReduction;

class ConstT    { ... }
class VarT      { ... }
class AlphaVarT { ... }
class LamT      { ... }
class AppT      { ... }
role  Term      { ... }


role Value {
}

role Applicable {
    method apply                (Value $arg --> Value:D)    { !!! }
}

role Term
    does Tree
    #does MethodFixedPoint
    does FreeVars[Term, ConstT, VarT, AppT, LamT]
    does Substitution[Term, ConstT, VarT, AppT, LamT]
    does EtaReduction[Term, ConstT, VarT, AppT, LamT]
{

    #method alpha-needy-terms(@vars) { !!! }

    #method eval         ($env --> Value) { !!! }
    #method eval-s       ( --> Value:D)   { !!! }

    # beta reduction (AppT is the only candidate):
    method isBetaRedex      (--> Bool) { False } # β-redex? - ie of form ((λx.B) z)
    method isBetaReducible  (--> Bool) { False } # either self.isBetaRedex or func is or arg is
    method beta-contract    (--> Term) { self  } # one-step β-simplification (either of self or inv or arg)
    method beta-reduce      (--> Term) { self.mfp(*.beta-contract) }

}


role LeafTerm does Term {
    method children { @() }

    method alpha-needy-terms(@vars) { @() }
}



class ConstT does LeafTerm does Value {
    has $.value;

    submethod BUILD(:$!value!) {
    }

    method eval($env) {
        $!value
    }

    method eval-s() {
        say "evaluating " ~ self ~ ' (self-evaluating)';
        $!value
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

    method eval($env) { $env.lookup($!name) }

    method eval-s() {
        die "cannot eval unbound var $!name";
    }
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

    method isBetaRedex {
        # (P Q) is a β-redex if P is of form (λx.B).
        # If so, it β-contracts to [P/x] B, ie P substituted for x
        # in the λ's body but beware: any free var in P
        # must NOT be accidentally captured by a binding in B.
        # If that would be the case, we need to α-convert before.
        ($!func ~~ LamT)
    }

    method alpha-problematic {
        return @() unless self.isBetaRedex;
        $!arg.freeVars.grep({ $!func.var.isFreeUnder(:binder($_), :in($!func.body)) });
    }

    method isBetaReducible {
        self.isBetaRedex
        || $!func.isBetaReducible
        || $!arg.isBetaReducible
    }

    method beta-contract {
        return self unless self.isBetaReducible;

        if (self.isBetaRedex) {
            !!!
        } elsif $!func.isBetaReducible {
            return AppT.new(:func($!func.beta-contract), :$!arg);
        } elsif $!arg.isBetaReducible {
            return AppT.new(:$!func, :arg($!arg.beta-contract));
        }
    }

    method eval($env) {
        my $code = $!func.eval($env);
        $code.apply($!arg.eval($env));
    }

    method eval-s() {
        say "evaluating " ~ self;
        my Applicable $f = $!func.eval-s;
        my $result = $f.apply($!arg.eval-s);
        say "        -> " ~ $result;
        $result;
    }
}

class LamT does Term does Applicable does Value {
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

    method eval($env) {
        return -> $arg {
            my $newEnv = $env.newFrame($!var => $arg);
            $!body.eval($newEnv);
        };
    }

    method eval-s() {
        say "evaluating " ~ self ~ ' (self-evaluating)';
        return self;
    }

    method apply(Value:D $arg --> Value) {
        say "applying " ~ self ~ " to $arg";
        my $result = $!body.subst($!var, :for($arg)).eval-s;
        say "      -> $result";
        $result;
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