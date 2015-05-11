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

    my sub mkSCall(str $fnName, *@args) {
        mkCall(lexVar($fnName), |@args);
    }

    my sub mkHashLookup($hash, str :$key!) {
        QAST::Op.new(:op<atkey>,
            $hash,
            QAST::SVal.new(:value($key)),
        )
    }

    my sub mkListLookup($list, int :$index!) {
        QAST::Op.new(:op<atpos>,
            $list,
            QAST::IVal.new(:value($index)),
        )
    }

    my $_strOut := lexVar('.strOut');
    my $_strLit := lexVar('.strLit');
    my $_apply1 := lexVar('.apply1');
    my $_isLambda := lexVar('.lambda?');

    my sub mkConcat(*@args) {
        if nqp::elems(@args) < 1 {
            nqp::die("need at least 1 arg for mkConcat");
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

    my sub mkDie(*@msgPieces) {
        QAST::Op.new(:op<die>, mkConcat("ERROR: ", |@msgPieces));
    }

    has $!lamCount;

    my sub mkSetting() {
        my $init := QAST::Stmts.new();
        my $block := QAST::Block.new($init);
        
        my $_isLambda-x := lexVar('x');
        $init.push(QAST::Op.new(:op<bind>, $_isLambda.declV,
            QAST::Block.new(:arity(1), QAST::Stmts.new(
                $_isLambda-x.declP,
                QAST::Op.new(:op<if>,
                    QAST::Op.new(:op<islist>, $_isLambda-x),
                    QAST::Op.new(:op<if>,
                        QAST::Op.new(:op<iseq_s>,
                            QAST::SVal.new(:value('λ')),
                            mkListLookup($_isLambda-x, :index(0)),
                        ),
                        QAST::IVal.new(:value(1)),
                        QAST::IVal.new(:value(0))
                    ),
                    QAST::IVal.new(:value(0))
                )
            ))
        ));

        my $_strOut-p1 := lexVar('v');
        $init.push(QAST::Op.new(:op<bind>, $_strOut.declV,
            QAST::Block.new(:arity(1), QAST::Stmts.new(
                $_strOut-p1.declP,
                QAST::Op.new(:op<if>,
                    QAST::Op.new(:op<isstr>, $_strOut-p1),
                    mkSCall('.strLit', $_strOut-p1),
                    QAST::Op.new(:op<if>,
                        mkSCall('.lambda?', $_strOut-p1),
                        mkListLookup($_strOut-p1, :index(2)),
                        QAST::Op.new(:op<reprname>,
                            $_strOut-p1
                        )
                    )
                )
            ))
        ));
        
        my $_strLit-p1 := lexVar('v');
        $init.push(QAST::Op.new(:op<bind>, $_strLit.declV,
            QAST::Block.new(:arity(1), QAST::Stmts.new(
                $_strLit-p1.declP,
                mkConcat('"', QAST::Op.new(:op<escape>, $_strLit-p1), '"')
            ))
        ));
        
        my $_apply1-f  := lexVar('f');
        my $_apply1-a1 := lexVar('a1');
        $init.push(QAST::Op.new(:op<bind>, $_apply1.declV,
            QAST::Block.new(:arity(2), QAST::Stmts.new(
                $_apply1-f.declP,
                $_apply1-a1.declP,
                QAST::Op.new(:op<if>,
                    mkSCall('.lambda?', $_apply1-f),
                    QAST::Op.new(:op<bind>, $_apply1-f,
                        mkListLookup($_apply1-f, :index(1))
                    ),
                    QAST::Op.new(:op<unless>,
                        QAST::Op.new(:op<isinvokable>, $_apply1-f),
                        mkDie('cannot apply ', mkCall($_strLit, $_apply1-f), ' to ', mkCall($_strOut, $_apply1-a1))
                    )
                ),
                QAST::Op.new(:op<call>,
                    $_apply1-f,
                    $_apply1-a1
                )
            ))
        ));

        return $block;
    }

    method TOP($/) {
        my $outVar := locVar('out');
        my $s := mkSetting();
        
        $s[0].push(QAST::Op.new(:op<say>, mkConcat(~$!lamCount, " lambdas\n------------------------------------------------")));
        #$s[0].push(QAST::Op.new(:op<flushfh>, QAST::Op.new(:op<getstdout>)));
        
        $s[0].push(mkSCall('.strOut', $/<termlist1orMore>.ast));
        
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
            QAST::Op.new(:op('call'), $f[1], $a);
        } else {
            mkSCall('.apply1', $f, $a);
        }
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
        my $binder := lexVar(~$/<varName>).declP;
        my $body   := $/<body>.ast;

        my $block := QAST::Block.new(:node($/), $binder, $body);

        my $lam := QAST::Op.new(:op<list>,
            QAST::SVal.new(:value('λ')),
            $block,
            QAST::SVal.new(:value(~$/)),
        );
        
        $lam.annotate('id', 'λ' ~ $!lamCount);
        $!lamCount++;
        
        make $lam;
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
    $c.parseactions(LActions.new);
    $c.command_line(@ARGS, :encoding('utf8'));
}
