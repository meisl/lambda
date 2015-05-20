use NQPHLL;



grammar LGrammar is HLL::Grammar {

    rule TOP {
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
        <-[\"\\βδλ&.()\s]>+
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

    token abstraction {
        <.lambda> <varName> '.'  <body=.termlist1orMore>
    }

    rule definition {
        '(' <.delta> <symbol> <term> ')'
    }
}

