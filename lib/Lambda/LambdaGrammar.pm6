use v6;

use Lambda::TermADT;


grammar LambdaGrammar {

    sub makeLeftAssoc(@operands! where *.elems >= 1, @operators = 0..* --> TTerm) is export {
        for @operands -> $n {
            die "expected TTerm but got " ~ $n.perl
                unless ($n ~~ TTerm) && $n.defined;
        }
        my $term = @operands[0];
        for @operators Z @operands[1..*] -> $op, $right {
            $term = $AppT($term, $right);
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

    token lambda { \\ | 'λ' }

    token delta { 'δ' }

    token variable {
        $<name> = <-[\\αβδλ.()\s]>+
        { make $VarT($<name>.Str) }
    }

    token constant {
        <!>     # none for now, ie we're in *pure* lambda calculus
    }

    token abstraction {
        \s* <.lambda> \s* <variable> \s* '.'  <body=.termlist1orMore> \s*
        { make $LamT($<variable>.ast, $<body>.ast) }
    }

    rule definition {
        '(' <.delta> $<symbol> = <.variable> <term> ')'
        {
            die "DefNode NYI";
            #make DefNode.new(:symbol($<symbol>.ast), :term($<term>.ast))
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

my sub parseLambda(Str:D $s --> TTerm) is export {
    #use Grammar::Tracer_01_h04;
    my $match = LambdaGrammar.subparse($s);
    #say ConstT.ctorCalls ~ " constructor calls.\n";
    #say "AST:\n$out\n";
    ($match.ast ~~ TTerm) && $match.ast || die X::Lambda::SyntaxError.new(:$match)
}
