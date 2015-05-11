use NQPHLL;



grammar LGrammar is HLL::Grammar {

    rule TOP {
        ^ <termlist1orMore> $
    }

    token termlist1orMore() {
        <term>**1..*
    }

    token termlist2orMore {
        <term>**2..* 
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
    }

    token lambda { \\ | 'λ' | '&' }

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
        \s* <.lambda> <varName> '.'  <body=.termlist1orMore>
    }

    rule definition {
        '(' <.delta> <symbol> <term> ')'
    }
}


class LActions is HLL::Actions {

    my role Var {
        method declV() {
            QAST::Var.new(:name(self.name), :scope(self.scope), :decl<var>);
        }
        method declP() {
            QAST::Var.new(:name(self.name), :scope(self.scope), :decl<param>);
        }
    }

    my sub locVar(str $name) {
        my $out := QAST::Var.new(:$name, :scope<local>);
        $out.HOW.mixin($out, Var);
        $out;
    }

    my sub lexVar(str $name) {
        my $out := QAST::Var.new(:$name, :scope<lexical>);
        $out.HOW.mixin($out, Var);
        $out;
    }

    my sub mkCall($fVar, *@args) {
        if nqp::istype($fVar, QAST::Var) {
            my $out := QAST::Op.new(:op<call>, $fVar);
            for @args {
                $out.push($_);
            }
            return $out;
        }
        nqp::die("invalid invocant " ~ $fVar.dump());
    }

    my sub mkHashLookup($hash, str :$key!) {
        QAST::Op.new(:op<atkey>,
            $hash,
            QAST::SVal.new(:value($key)),
        )
    }

    my $_strOut := lexVar('.strOut');
    my $_strLit := lexVar('.strLit');

    my sub mkConcat(*@args) {
        if nqp::elems(@args) < 2 {
            nqp::die("need at least 2 args for mkConcat");
        }
        my @nodes := [];
        for @args { # map any str to an SVal
            if nqp::isstr($_) {
                nqp::push(@nodes, QAST::SVal.new(:value($_)));
            } else {
                #say('###' ~ $_.dump);
                nqp::push(@nodes, $_);
            }
        }

        my @compressed := [];
        my $current := nqp::shift(@nodes);
        for @nodes {
            if nqp::istype($current, QAST::SVal) && nqp::istype($_, QAST::SVal) {
                $current.value($current.value ~ $_.value);
            } else {
                nqp::push(@compressed, $current);
                $current := $_;
            }
        }
        nqp::push(@compressed, $current);

        if nqp::elems(@compressed) > 1 {
            $current := nqp::shift(@compressed);
            for @compressed {
                $current := QAST::Op.new(:op<concat>, $current, $_)
            }
        }

        return $current;
    }

    my sub mkSetting() {

        my $block := QAST::Block.new(QAST::Stmts.new());
        
        my $_strOut-p1 := lexVar('v');
        $block[0].push(QAST::Op.new(:op<bind>, $_strOut.declV,
            QAST::Block.new(:arity(1), QAST::Stmts.new(
                $_strOut-p1.declP,
                QAST::Op.new(:op<if>,
                    QAST::Op.new(:op<isstr>, $_strOut-p1),
                    mkCall($_strLit, $_strOut-p1),
                    QAST::Op.new(:op<if>,
                        QAST::Op.new(:op<ishash>,
                            $_strOut-p1
                        ),
                        mkHashLookup($_strOut-p1, :key<lambda>),
                        QAST::Op.new(:op<reprname>,
                            $_strOut-p1
                        )
                    )
                )
            ))
        ));
        
        my $_strLit-p1 := lexVar('v');
        $block[0].push(QAST::Op.new(:op<bind>, $_strLit.declV,
            QAST::Block.new(:arity(1), QAST::Stmts.new(
                $_strLit-p1.declP,
                mkConcat('"', QAST::Op.new(:op<escape>, $_strLit-p1), '"')
            ))
        ));
        
        $block;
    }

    method TOP($/) {
        my $outVar := locVar('out');
        my $s := mkSetting();
        $s[0].push(mkCall($_strOut, $/<termlist1orMore>.ast));
        make $s;
    }

    method termlist1orMore($/) {
        if nqp::elems($/<term>) == 1 {
#            say('####termlist1orMore: ' ~ ~$/<term>[0]);
            make $/<term>[0].ast;
        } else {
            self.termlist2orMore($/);
        }
    }

    my sub mkApp($f, $a) {
        if $f.has_ann('λ') {
            #say($f[0].value ~ ": ...");
            return QAST::Op.new(:op('call'), $f[1], $a);
        }
        my $subject := locVar('subject');
        QAST::Op.new(:op<call>, QAST::Block.new(
            QAST::Stmts.new(
                QAST::Op.new(:op<bind>,
                    $subject.declV,
                    $f
                ),
                QAST::Op.new(:op<if>,
                    QAST::Op.new(:op<ishash>, $subject),
                    QAST::Op.new(:op('call'),
                        mkHashLookup($subject, :key<code>),
                        $a
                    ),
                    QAST::Op.new(:op<die>,
                        mkConcat('cannot apply ', mkCall($_strLit, $subject), ' to ', mkCall($_strOut, $a))
                    )
                )
            )
        ))
    }

    method termlist2orMore($/) {
        my $f := $/<term>.shift.ast;
        my $a := $/<term>.shift.ast;
        my $app := mkApp($f, $a);

        for $/<term> {
            $app := mkApp($app, $_.ast);
        }
        make QAST::Stmts.new(:node($/), $app);
    }

    method term($/) {
        make $/<t>.ast;
    }

    method variable($/) {
        my $var := QAST::Var.new(:name($/), :scope('lexical'), :node($/));
        make $var;
    }

    my %str-esc := hash(:b("\b"), :r("\r"), :n("\n"), :f("\f"), :t("\t"));
    nqp::bindkey(%str-esc, '"', '"');
    nqp::bindkey(%str-esc, '\\', '\\');

    method str-constant($/) {
#        say("###str-constant, 0: " ~ nqp::elems($/[0]));
        my $s := "";
        for $/[0] {
            if nqp::substr($_, 0, 1) eq '\\'  {
                my $esc := nqp::substr($_, 1, 1);
                if nqp::existskey(%str-esc, $esc) {
                    $s := $s ~ %str-esc{$esc};
                } else {
                    nqp::die("unknown escape sequence \\" ~ $esc);
                }
            } else {
                $s := $s ~ $_;
            }
        }
#        say("###str-constant: " ~ $s);
        make QAST::SVal.new(:value($s));
    }

    method abstraction($/) {
        my $binder := QAST::Var.new(:name($/<varName>), :scope('lexical'), :decl('param'));
        my $body   := $/<body>.ast;

        my $block := QAST::Block.new(:node($/), $binder, $body);

        my $hash := QAST::Op.new(:op<hash>,
            QAST::SVal.new(:value<code>),   $block,
            QAST::SVal.new(:value<lambda>), QAST::SVal.new(:value(~$/)), 
            #QAST::SVal.new(:value<qast>),   QAST::WVal.new(:value($block)),
        );
        
        $hash.annotate('λ', 1);

        make $hash;
    }
}

class LCompiler is HLL::Compiler {
    method command_line(@args, *%adverbs) {
        my $program-name := @args[0];
        my $res  := self.process_args(@args);
        my %opts := $res.options;
        my @a    := $res.arguments;

        for %opts {
            %adverbs{$_.key} := $_.value;
        }
        self.usage($program-name) if %adverbs<help>  || %adverbs<h>;
        
        #if $!backend.is_precomp_stage(%adverbs<target>) {
        #    %adverbs<precomp> := 1;
        #}

        #self.command_eval(|@a, |%adverbs);
        
        my $result := self.evalfiles(|@a, :encoding('utf8'), |%adverbs);
        self.interactive_result($result);
    }
}

sub MAIN(*@ARGS) {
    my $c := LCompiler.new();
    $c.language('lambda');
    $c.parsegrammar(LGrammar);
    $c.parseactions(LActions);
    $c.command_line(@ARGS, :encoding('utf8'));
}
