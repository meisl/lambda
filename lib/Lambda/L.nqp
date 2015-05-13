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
            my $out := nqp::clone(self);
            $out.decl('var');
            $out;
        }
        method declP() {
            my $out := nqp::clone(self);
            $out.decl('param');
            $out;
        }
    }

    my sub locVar(str $name, *%adverbs) {
        my $out := QAST::Var.new(
            :name($name),
            :scope<local>,
            |%adverbs
        );
        $out.HOW.mixin($out, Var);
        $out;
    }

    my sub lexVar(str $name, *%adverbs) {
        my $out := QAST::Var.new(
            :name($name),
            :scope<lexical>,
            |%adverbs
        );
        $out.HOW.mixin($out, Var);
        $out;
    }

    my sub asNode($v) {
        if nqp::isstr($v) {
            QAST::SVal.new(:value($v));
        } elsif nqp::isint($v) {
            QAST::IVal.new(:value($v));
        } elsif nqp::isnum($v) {
            QAST::NVal.new(:value($v));
        } elsif nqp::istype($v, QAST::Node) {
            $v;
        } else {
            die("cannot turn " ~ $v ~ " into a QAST::Node");
        }
    }

    my sub mkCall($fVar, *@args) {
        my $out := QAST::Op.new(:op<call>, $fVar);
        for @args {
            $out.push(asNode($_));
        }
        return $out;
    }

    my sub mkSCall(str $fnName, *@args) {
        if $fnName eq '.ifTag' {
            my @as := [];
            @as.push(asNode(@args.shift));
            @as.push(asNode(@args.shift));
            for @args {
                if nqp::istype($_, QAST::Block) && ($_.arity == 0) {
                    @as.push($_);
                } else {
                    @as.push(QAST::Block.new(:arity(0), QAST::Stmt.new(asNode($_))));
                }
            };
            mkCall(lexVar($fnName), |@as);
        } else {
            mkCall(lexVar($fnName), |@args);
        }
    }

    my sub mkHashLookup($hash, :$key!) {
        if nqp::isstr($key) || nqp::istype($key, QAST::Node) {
            QAST::Op.new( :op<atkey>, $hash, asNode($key) );
        } else {
            die("need str or QAST::SVal as key");
        }
    }

    my sub mkListLookup($list, :$index!) {
        if nqp::isint($index) || nqp::istype($index, QAST::Node) {
            QAST::Op.new( :op<atpos>, $list, asNode($index) );
        } else {
            die("need int or QAST::IVal as index");
        }
    }

    my sub mkConcat(*@args) {
        if nqp::elems(@args) < 1 {
            nqp::die("need at least 1 arg for mkConcat");
        }
        my @nodes := [];
        for @args { # map any str to an SVal
            if nqp::isstr($_) {
                nqp::push(@nodes, asNode($_));
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
        QAST::Op.new(:op<die>, mkConcat('ERROR: ', |@msgPieces));
    }

    my sub mkLambda2code($subject) {
        mkSCall('.->#n', $subject, 'λ', 1);
    }

    my sub mkLambda2str($subject) {
        mkSCall('.->#n', $subject, 'λ', 2);
    }

    has $!lamCount;

    my sub mkSetting() {
        my $init := QAST::Stmts.new();
        my $block := QAST::Block.new($init);
        
        my $_ifTag-s := lexVar('s');    # "subject"
        my $_ifTag-x := lexVar('x');
        my $_ifTag-t := lexVar('t');
        my $_ifTag-e := lexVar('e');
        $init.push(QAST::Op.new(:op<bind>, lexVar('.ifTag').declV,
            QAST::Block.new(:arity(4), QAST::Stmts.new(
                $_ifTag-s.declP,
                $_ifTag-x.declP,
                $_ifTag-t.declP,
                $_ifTag-e.declP,
                mkCall( # expects 0-arity block as "then" and "else" args (taken care of by mkSCall)
                    QAST::Op.new(:op<if>,
                        QAST::Op.new(:op<islist>, $_ifTag-s),
                        QAST::Op.new(:op<if>,
                            QAST::Op.new(:op<iseq_s>,
                                $_ifTag-x,
                                mkListLookup($_ifTag-s, :index(0)),
                            ),
                            $_ifTag-t,
                            $_ifTag-e
                        ),
                        $_ifTag-e
                    )
                )
            ))
        ));

        my $_project-s := lexVar('s');  # "subject"
        my $_project-t := lexVar('t');  # "tag"
        my $_project-i := lexVar('i');  # "index"
        $init.push(QAST::Op.new(:op<bind>, lexVar('.->#n').declV,
            QAST::Block.new(:arity(1), QAST::Stmts.new(
                $_project-s.declP,
                $_project-t.declP,
                $_project-i.declP,
                mkSCall('.ifTag', $_project-s, $_project-t,
                    mkListLookup($_project-s, :index($_project-i)),
                    QAST::Op.new(:op<null>)
                )
            ))
        ));

        my $_strOut-p1 := lexVar('v');
        $init.push(QAST::Op.new(:op<bind>, lexVar('.strOut').declV,
            QAST::Block.new(:arity(1), QAST::Stmts.new(
                $_strOut-p1.declP,
                QAST::Op.new(:op<if>,
                    QAST::Op.new(:op<isstr>, $_strOut-p1),
                    mkSCall('.strLit', $_strOut-p1),
                    QAST::Op.new(:op<defor>,
                        mkLambda2str($_strOut-p1),
                        QAST::Op.new(:op<reprname>,
                            $_strOut-p1
                        )
                    )
                )
            ))
        ));
        
        my $_strLit-p1 := lexVar('v');
        $init.push(QAST::Op.new(:op<bind>, lexVar('.strLit').declV,
            QAST::Block.new(:arity(1), QAST::Stmts.new(
                $_strLit-p1.declP,
                mkConcat('"', QAST::Op.new(:op<escape>, $_strLit-p1), '"')
            ))
        ));
        
        my $_apply1-f  := lexVar('f');
        my $_apply1-a1 := lexVar('a1');
        $init.push(QAST::Op.new(:op<bind>, lexVar('.apply1').declV,
            QAST::Block.new(:arity(2), QAST::Stmts.new(
                $_apply1-f.declP,
                $_apply1-a1.declP,
                QAST::Op.new(:op<call>,
                    QAST::Op.new(:op<defor>,
                        mkLambda2code($_apply1-f),
                        QAST::Op.new(:op<if>,
                            QAST::Op.new(:op<isinvokable>, $_apply1-f),
                            $_apply1-f,
                            mkDie('cannot apply ', mkSCall('.strLit', $_apply1-f), ' to ', mkSCall('.strOut', $_apply1-a1))
                        )
                    ),
                    $_apply1-a1
                )
            ))
        ));

        return $block;
    }

    my sub reportFV(str $where, $match, %fvs) {
        say(nqp::elems(%fvs), " FVs in $where @ ", '"', nqp::escape($match), '"');
        for %fvs {
            say('    ', nqp::iterkey_s($_), ' => ', nqp::iterval($_));
        }
    }

    method TOP($/) {
        my $mainExpr := $/<termlist1orMore>.ast;

        my $fvs := $mainExpr.ann('FV');
        if nqp::elems($fvs) > 0 {
            my $msg := "Compile Error: unbound variables ";
            for $fvs {
                $msg := $msg ~ nqp::iterkey_s($_) ~ " ";
            }
            nqp::die($msg);
        }

        my $s := mkSetting();
        
        $s[0].push(QAST::Op.new(:op<say>, mkConcat(~$!lamCount, " lambdas\n------------------------------------------------")));
        #$s[0].push(QAST::Op.new(:op<flushfh>, QAST::Op.new(:op<getstdout>)));
        
        $s[0].push(mkSCall('.strOut', $mainExpr));
        
        make $s;
    }

    method termlist1orMore($/) {
        if nqp::elems($/<term>) == 1 {
#            say('####termlist1orMore: ' ~ ~$/<term>[0]);
            my $out := $/<term>[0].ast;
            reportFV('termlist1orMore', $/, $out.ann('FV'));
            make $out;
        } else {
            self.termlist2orMore($/);
        }
    }

    my sub mkApp($f, $a) {
        my $out;
        if $f.has_ann('λ') {
            #say($f[0].value ~ ": ...");
            $out := QAST::Op.new(:op('call'), $f[1], $a);
        } else {
            $out := mkSCall('.apply1', $f, $a);
        }
        my $fv := nqp::clone($f.ann('FV'));
        for $a.ann('FV') {
            $fv{nqp::iterkey_s($_)} := nqp::iterval($_);
        }
        $out.annotate('FV', $fv);

        $out;
    }

    method termlist2orMore($/) {
        my $f := $/<term>.shift.ast;
        my $a := $/<term>.shift.ast;
        my $app := mkApp($f, $a);

        for $/<term> {
            $app := mkApp($app, $_.ast);
        }
        my $out := QAST::Stmts.new(:node($/), $app);
        $out.annotate('FV', $app.ann('FV'));
        reportFV('termlist2orMore', $/, $out.ann('FV'));
        make $out;
    }

    method term($/) {
        my $out := $/<t>.ast;
        reportFV('term', $/, $out.ann('FV'));
        make $out;
    }

    method variable($/) {
        my str $name := ~$/;
        my $var := lexVar($name, :node($/));
        my $fv := hash();
        $fv{$name} := 1;
        $var.annotate('FV', $fv);
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
        my $out := asNode($s);
        $out.annotate('FV', hash());
        make $out;
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

        if !$body.has_ann('FV') {
            nqp::die("missing annotation 'FV' in body " ~ $/<body>);
        }

        my $fv := nqp::clone($body.ann('FV'));
        nqp::deletekey($fv, $/<varName>);
        $lam.annotate('FV', $fv);
        
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
