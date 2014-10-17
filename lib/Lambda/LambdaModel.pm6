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
    method isLiteralIdentity    (           --> Bool:D)     { !!! }
    method isEquivToIdentity    (           --> Bool:D)     { !!! }
}

role Term
    does Tree
    does MethodFixedPoint
    does FreeVars[Term, ConstT, VarT, AppT, LamT]
    does Substitution[Term, ConstT, VarT, AppT, LamT]
    does EtaReduction[Term, ConstT, VarT, AppT, LamT]
{

    #method alpha-needy-terms(@vars) { !!! }

    #method eval         ($env --> Value) { !!! }
    #method eval-s       ( --> Value:D)   { !!! }
    #method simplify     ( --> Term:D)  { !!! }

    # eta reduction (LamT is the only candidate):
    method isEtaReducible   (--> Bool) { False } # either self.isEtaRedex or body isEtaReducible
    method eta-contract     (--> Term) { self  } # one-step η-simplification (either of self or body)
    method eta-reduce       (--> Term) { self.mfp(*.eta-contract) }

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

    method simplify( --> Term) {
        return self;
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

    method eval($env) { $env.lookup($!name) }

    method eval-s() {
        die "cannot eval unbound var $!name";
    }

    method simplify( --> Term) {
        return self;
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

    method simplify( --> Term) {
        # TODO: AppT.simplify: memoize or do simplify in constructor
        # TODO: AppT.simplify: return self if simplification of both, func and arg didn't change anything
        my $simp-inv = $!func.simplify;
        my $simp-arg = $!arg.simplify;
        return ($simp-inv ~~ Applicable) && $simp-inv.isLiteralIdentity
            ?? $simp-arg
            !! AppT.new(:func($simp-inv), :arg($simp-arg));
    }

    method gist { '(' ~ $!func.gist ~ ' ' ~ $!arg ~ ')' }
}

class LamT does Term does Applicable does Value {
    has VarT:D $.var;
    has Term:D $.body;

    submethod BUILD(VarT:D :$!var!, Term:D :$!body!) {
    }

    method children { @($!var, $!body) }

    method gist {
        "(λ$!var." ~ $!body.gist ~ ')';
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

    method isEtaReducible {
        self.isEtaRedex || $!body.isEtaReducible
    }

    method eta-contract {
        return $!body.func
            if self.isEtaRedex;

        return $!body.isEtaReducible
            ?? LamT.new(:$!var, :body($!body.eta-contract))
            !! self;
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

    method simplify( --> Term) {
        self.simplify-curry;
    }

    # eta-reduction
    method simplify-curry( --> Term) {
        # TODO: LamT.simplify: memoize or simplify in ctor
        my $simp-body = $!body.simplify;
        return ($simp-body ~~ AppT)
            && ($simp-body.arg ~~ VarT) 
            && $!var.isNotFree(:in(!$simp-body.func))
            && ($simp-body.arg.name ~~ $!var.name)
            ?? $simp-body.func
            # TODO: LamT.simplify: if simplified body doesn't change anything return self
            !! LamT.new(:$!var, :body($simp-body))
        ;
    }

    method isEquivToIdentity (--> Bool:D) {
        !!! 
        # self.BetaEtaReduce.isLiteralIdentity
    }

    method isLiteralIdentity (--> Bool:D) {
        ($!body ~~ VarT) && ($!var.name eq $!body.name);
    }


    method apply(Value:D $arg --> Value) {
        say "applying " ~ self ~ " to $arg";
        my $result = $!body.subst($!var, :for($arg)).eval-s;
        say "      -> $result";
        $result;
    }

}


my $x = VarT.get('x');
my $y = VarT.get('y');
my $z = VarT.get('z');
my $lam = LamT.new(
    :var($x),
    :body(AppT.new( :func($x), :arg($y) ))
);

say '$lam: ' ~ $lam;
say '$lam.subst($y, :for($x)): ' ~ $lam.subst($y, :for($x));
say '$lam.subst($z, :for($y)): ' ~ $lam.subst($z, :for($y));

#say $lam.alpha-convert($z, :for($lam.var));