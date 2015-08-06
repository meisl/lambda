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

        ^ \s* 
          <.eolComment>*
          [  <termlist1orMore> $
          || $ { panic($/, 'empty input') }
          ]
    }

    token termlist1orMore() {
        <term>**1..*
        \s* <.eolComment>*
    }

    token termlist2orMore {
        <term>**2..*
        \s* <.eolComment>*
    }

    token term {
        \s* <.eolComment>*
        [  <t=variable>
        || <t=str-constant>
        || <t=int-constant>
        #|| <t=definition>
        || <t=abstraction>
        || '(' \s* <.eolComment>*
               [  <t=abstraction>
               || <t=simple-let>
               || <t=termlist2orMore>
               ]
          ')'
        ]
        \s* <.eolComment>*
    }

    token eolComment {
        '#' <-[\v]>* \s*
    }

    token lambda { 'λ' || \\ || '&' }

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
        [  (<-[\n\"\\]>+)
        || (\\ [ <[brnft\"\\]> || . { panic($/, "invalid escape sequence " ~ $/) } ])
        ]*
        '"'
    } 

    token int-constant {
        \d+     { panic($/, 'NYI') }
    }


    my sub match2location($match) {
        my $file := $*USER_FILE;
        my @lines := nqp::split("\n", nqp::substr($match.orig, 0, $match.from == 0 ?? $match.chars !! $match.from));
        my $colN;
        my $lineN := nqp::elems(@lines);
        if $lineN == 0 {
            $lineN := 1;
            $colN := 1;
        } else {
            $colN  := 1 + nqp::chars(@lines.pop);
        }
        hash(:file($file), :line($lineN), :column($colN), :match($match), :str("$file:$lineN:$colN"));
    }

    my sub loc2str(%l) {
        my $varNameStr := nqp::existskey(%l, 'var')
            ?? '  (' ~ %l<var>.name ~ ')'
            !! ''
        ;
        '   at ' ~ %l<str> ~ $varNameStr;
    }

    sub panic($match, *@msg-pieces) {
        @msg-pieces.push("\n");
        @msg-pieces.push(loc2str(match2location($match)));
        nqp::die(join('', @msg-pieces));
    }

    token abstraction {
        <lambda>
        [  <varName>
        || $<s> = \s+   { panic($<s>, 'no white space allowed after "' ~ $/<lambda>) }
        ||              <.bogus: 'invalid lambda binder'>
        ]
        [  '.'
        || $<bogus> = <-[.()\"\\]>* {   # matches whitespace, too
               panic($<bogus>, 'expected "." (dot) right after "' ~ $/<lambda> ~ $/<varName> ~ '"') 
           }
        ]
        [  <body=.termlist1orMore>
        || <.bogus: 'invalid term in lambda body'>
        ]
        \s* <.eolComment>*
    }

    token simple-let {
        <delta> 
        [  \s+ <.eolComment>*
        || <.eolComment>+
        || [\S|$] { panic($/, 'need whitespace after "' ~ $/<delta> ~ '"') }
        ]
        '(' \s* <.eolComment>*
            <bindings=.simple-let-binding>+
        ')'
        \s* <.eolComment>*
        <body=.termlist1orMore>
        \s* <.eolComment>*
    }

    token simple-let-binding {
        '(' [  <binder=.variable>
            || <.bogus: 'invalid binder "' ~ $/<binder> ~ '" in simple let'>
            ]
            \s+ <.eolComment>*
            [  <body=.term>
            || <app=.termlist2orMore> { panic($/<app>, 'invalid binding of "' ~ $/<binder> ~ '" in simple let: need parens around "' ~ $/<app> ~ '"') }
            ]
        ')'
        \s* <.eolComment>*
    }

    token bogus($msg) {
        <-[\s.()\"\\]>*  { panic($/, $msg, ' "' ~ $/ ~ '"') }
    }

}

