use v6;
use Lambda::LambdaModel;


my %texts = %(              # chi: χ0
    1 => '(λx.(x (λa.(λb.a))))',
    2 => 'λx.x λa.λb.a',
    7 => 'λx.x',
    3 => '(f _)',
    8 => '(δ id λx.x)',

    # Church numerals
    9 => '(δ χ0 λf.λx.x)  (δ χ1 λf.λx.f x)  (δ χ2 λf.λx.f (f x))  (δ χ3 λf.λx.f (f (f x)))'
        #'(δ χ0 λf.id)    (δ χ1 id)'
         ~'  (δ succ λn.λf.λx.n f (f x))',
         #'  (δ succ λn.λf.λx.f (n f x))',
    4 => '(δ id λx.x)  (δ fst λa.λb.a)  (δ snd λa.λb.b)  (δ reverse-apply λa.λf.f a)  (δ car (reverse-apply fst))',
    5 => '(δ id λx.x)  (δ fst λa.λb.a)  (δ snd λa.λb.b)',
    6 => '(δ let λvar.λterm.λbody.(λvar.body) term)',
    10 => '(λa.λb.a) (λf.λx.x) (λf.f)',
);



grammar LambdaGrammar {

    sub makeLeftAssoc(@operands! where *.elems >= 1, @operators = 0..* --> Term) is export {
        for @operands -> $n {
            die "expected Term but got " ~ $n.perl
                unless ($n ~~ Term) && $n.defined;
        }
        my $term = @operands[0];
        for @operators Z @operands[1..*] -> $op, $right {
            $term = AppT.new(:func($term), :arg($right));
        }
        $term;
    }

    my sub termlist2node(@terms) {
        makeLeftAssoc(@terms.map(*.ast));
    }

    rule TOP {
        ^ <termlist1orMore> $
        { make $<termlist1orMore>.ast }
    }

    token termlist1orMore() {
        <term>**1..*
        { make termlist2node($<term>) }
    }

    token termlist2orMore {
        <term>**2..* 
        { make termlist2node($<term>) }
    }

    token term {
        \s*
        [
        | <t=variable>
        | <t=constant>
        | <t=definition>
        | <t=abstraction>
        | '(' <t=abstraction> ')'
        | '(' <t=termlist2orMore> ')'
        ] \s*
        { make $<t>.ast }
    }

    token lambda { \\ | λ }

    token delta { δ }

    token variable {
        $<name> = <-[\\αβδλ.()\s]>+
        { make VarT.get($<name>.Str) }
    }

    token constant {
        <!>     # none for now, ie we're in *pure* lambda calculus
    }

    token abstraction {
        \s* <.lambda> \s* <variable> \s* '.'  <body=.termlist1orMore> \s*
        { make LamT.new(:var($<variable>.ast), :body($<body>.ast)) }
    }

    rule definition {
        '(' <.delta> $<symbol> = <.variable> <term> ')'
        {
            make DefNode.new(:symbol($<symbol>.ast), :term($<term>.ast))
        }
    }
}

class X::Lambda::SyntaxError is Exception {
    has Str     $.message;
    has Match   $.match;

    submethod BUILD(Match:D :$!match) {
        my $to = $!match.to < 0 ?? $!match.orig.chars + $!match.to !! $!match.to;
        $to = max($to, 0);
        $!message = "Syntax error: "
            ~ ($to == 0 ?? 'HERE>>>' !! $!match.orig.substr(0, $to).perl ~ '<<<HERE>>>')
            ~ $!match.orig.substr($to).perl;
    }
}

my sub λ(Str:D $s --> Term) is export {
    #use Grammar::Tracer_01_h04;
    my $match = LambdaGrammar.subparse($s);
    #say ConstT.ctorCalls ~ " constructor calls.\n";
    #say "AST:\n$out\n";
    ($match.ast ~~ Term) && $match.ast || die X::Lambda::SyntaxError.new(:$match)
}

if False {
    #use Grammar::Tracer_01_h04;
    my grammar G is LambdaGrammar {}
    #my $match = G.doWork(7)[0];
    #my $n = $match.ast;
    #say $match;
    #say '';
    #say 'AST:';
    #say $n;
    my $succ-of-zero_a = '(λn.λf.λx.n f (f x)) (λf.λx.x)';
    my $succ-of-zero_b = '(λn.λf.λx.f (n f x)) (λf.λx.x)';

    my $test-simplify_curry = 'λf.λx.f x';
    my $test-simplify_ident = '(λx.x) (λx.x)';
    my $test-simplify_ident_a = '(λf.(λx.((λx.x) (f x))))';
    my $test-simplify_ident_b = '(λf.(λx.(f ((λx.x) x))))';
    
    my $omega = '(δ ω λx.x x) (δ Ω (ω ω))';
    my $growing = '(λx.x x y)(λx.x x y)';

    my $n;

    #say λ('(z x (y λx.λy.x y z))').freeVars;
    #exit;

    $n = λ('(λx.λz.λv.z x (λx.x) λz.x z) ((z ((λx.λy.x y z) x)) v)');
    my $func = $n.func;
    my $arg = $n.arg;
    say $n;
    say 'β-redex? '~ $n.isBetaRedex;
    say 'β-reducible? '~ $n.isBetaReducible;
    say 'FV: '~ $n.freeVars;
    say 'α-problematic: ' ~ $n.alpha-problematic;
    say "n.α-needy-terms:\n  " ~ $n.alpha-needy-terms($n.alpha-problematic).join("\n  ");
    say "apt.α-needy-terms:\n  " ~ $func.alpha-needy-terms($n.alpha-problematic).join("\n  ");

    say '';
    say $func;
    say 'β-redex? '~ $func.isBetaRedex;
    say 'β-reducible? '~ $func.isBetaReducible;
    say 'FV: '~ $func.freeVars;
    say 'x.isFreeUnder(:binder(z), :in(...)) ' ~ $func.var.isFreeUnder(:binder(VarT.get('z')), :in($func.body));
    say 'x.isFreeUnder(:binder(x), :in(...)) ' ~ $func.var.isFreeUnder(:binder(VarT.get('x')), :in($func.body));
    say 'x.isFreeUnder(:binder(v), :in(...)) ' ~ $func.var.isFreeUnder(:binder(VarT.get('v')), :in($func.body));

    say $arg;
    say 'β-redex? '~ $arg.isBetaRedex;
    say 'β-reducible? '~ $arg.isBetaReducible;
    say 'FV: '~ $arg.freeVars;
    exit;

    #$n = λ('λf.(λx.λy.(f g h x y))');
    my $n_smp = $n.eta-contract;
    say "eta-contract (only):\n$n_smp\n";
    say $n_smp.isEtaReducible;
    say $n_smp.eta-contract;
    say $n.eta-reduce;

    my $n_evd = $n.eval-s;
    say "eval-s:\n$n_evd\n";
    say $n_evd;
    
    my $n_evd_smp = $n_evd.simplify;
    say "eval-s + simplify:\n$n_evd_smp\n";
    say $n_evd_smp;

    say ConstT.ctorCalls ~ " constructor calls.\n";

    #$succ-of-zero_a:
    #a: (λf.(λx.(((λg.(λx.x)) f) (f x))))
    #   (λf.(λx.(     (λx.x)     (f x))))   # App.simplify-ident
    #   (λf.(λx.                 (f x)))    # Abs.simplify-curry
    #   (λf.                      f)
 
    #b: (λf.(λx.(f (((λg.(λx.x)) f) x))))
    #   (λf.(λx.(f (     (λx.x)     x))))   # App.simplify-ident
    #   (λf.(λx.(f                  x)))    # Abs.simplify-curry
    #   (λf.     f)

}
