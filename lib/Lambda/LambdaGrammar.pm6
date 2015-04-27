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
        | <t=str-constant>
        | <t=int-constant>
        | <t=definition>
        | <t=abstraction>
        | '(' <t=abstraction> ')'
        | '(' <t=termlist2orMore> ')'
        ] \s*
        { make $<t>.ast }
    }

    token lambda { \\ | 'λ' }

    token delta { 'δ' }

    token varName {
        <-[\"\\βδλ.()\s]>+
    }

    token variable {
        <varName>
        { make $VarT($<varName>.Str) }
    }

    token symbol {
        <varName>
    }

    my %str-esc = %(b => "\b", r => "\r", n => "\n", f => "\f", t => "\t");
    token str-constant {
        '"'
        [ (<-[\"\n\\]>+)
        | \\ (<[\"\\]>)
        | \\ (<-[\"\n\\]>)    { $0[*-1].make(%str-esc{$0[*-1]} // (die 'unknown esc \\' ~ $0[*-1])) }
        ]*
        '"'
        { my $rawStr = $0.map({$_.ast // $_}).list.join;
          make $ConstT($rawStr);
        }
    } 

    token int-constant {
        <!>     # NYI
    }

    token abstraction {
        \s* <.lambda> \s* <varName> \s* '.'  <body=.termlist1orMore> \s*
        { make $LamT($<varName>.Str, $<body>.ast) }   # DONE: LamT_ctor_with_Str_binder
    }

    rule definition {
        '(' <.delta> <symbol> <term> ')'
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
