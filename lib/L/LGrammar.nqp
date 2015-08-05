use NQPHLL;

use Util;



# TODO: Unable to parse expression in blockoid; couldn't find final '}'  at line 143, near "$msg := $m"
=begin
{
    my $msg := nqp::join('', ['a',
        'b'
        'c'
    ]);
}
=end

grammar LGrammar is HLL::Grammar {

    rule TOP {
        :my $*UNIT := QAST::CompUnit.new(:hll('L'), QAST::Block.new());

        ^ \s* <.eolComment>* <termlist1orMore>? $
    }

    token termlist1orMore() {
        <term>**1..*
    }

    token termlist2orMore {
        <term>**2..* 
    }

    token term {
        \s* <.eolComment>*
        [
        | <t=variable>
        | <t=str-constant>
        | <t=int-constant>
        | <t=definition>
        | <t=abstraction>
        | '(' \s* <.eolComment>*
              [
              | <t=abstraction>
              | <t=termlist2orMore>
              ]
          ')'
        ]
        \s* <.eolComment>*
    }

    token eolComment {
        '#' <-[\v]>* \s*
    }

    token lambda { 'λ' | \\ | '&' }

    token delta { 'δ' }

    token varName {
        <-[\d\"\\βδλ&.()\s]>+
          <-[\"\\βδλ&.()\s]>*
    }

    token variable {
        <varName>
    }

    token symbol {
        <varName>
    }

    token str-constant {
        '"'
        [ (<-[\n\"\\]>+)
        | (\\ [ <[brnft\"\\]> || <.panic: "unknown escape sequence"> ])
        ]*
        '"'
    } 

    token int-constant {
        <!>     # NYI
    }


    my sub match2location($match) {
        my @lines := nqp::split("\n", nqp::substr($match.orig, 0, $match.from == 0 ?? $match.chars !! $match.from));
        my $lineN := nqp::elems(@lines);
        my $colN  := 1 + nqp::chars(@lines.pop);
        my $file := $*USER_FILE;
        hash(:file($file), :line($lineN), :column($colN), :match($match), :str("$file:$lineN:$colN"));
    }

    my sub loc2str(%l) {
        my $varNameStr := nqp::existskey(%l, 'var')
            ?? '  (' ~ %l<var>.name ~ ')'
            !! ''
        ;
        '   at ' ~ %l<str> ~ $varNameStr;
    }

    method panic($match, *@msg-pieces) {
        @msg-pieces.push("\n");
        @msg-pieces.push(loc2str(match2location($match)));
        nqp::die(join('', @msg-pieces));
    }

    token abstraction {
        :my $so-far := $/<lambda> ~ $/<varName>;
        <lambda>        { $so-far := $/<lambda> }
        [  <varName>    { $so-far := $so-far ~ $/<varName> }
        || <space-plus> { self.panic($/<space-plus>, 'no white space allowed after "' ~ $so-far ~ '"!') }
        ||              <.bogus: 'invalid lambda binder'>
        ]
        [  '.'
        || <.bogus-ws: 'expected "." (dot) right after "' ~ $so-far ~ '" - found'>
        ]
        [  <body=.termlist1orMore>
        || <.bogus: 'invalid term in lambda body'>
        ]
    }

    token definition {
        #<.panic: 'NYI'>
        '(' <.delta> \s*
            [  <symbol>
            || <.bogus: 'invalid definition symbol'>
            ]
            <body=.termlist1orMore>
         ')'
    }

    token space-plus {
        \s+
    }
    

    token bogus($msg) {
        <-[\s.()\"\\]>*  { self.panic($/, $msg, " \"$/\"") }
    }

    token bogus-ws($msg) {
        <-[.()\"\\]>*  { self.panic($/, $msg, " \"$/\"") }
    }

}

