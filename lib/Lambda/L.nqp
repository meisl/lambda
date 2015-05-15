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
        | '(' <t=abstraction> ')'
        | '(' <t=termlist2orMore> ')'
        ]
        \s* <.eolComment>*
    }

    token eolComment {
        '#' <-[\v]>* \s*
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

    my sub isForced($node) {
        if nqp::istype($node, QAST::Node) {
            nqp::istype($node, QAST::Op) && ($node.op eq 'call') && (nqp::elems($node.list) == 1);
        } else {
            nqp::die("expected a QAST::Node");
        }
    }

    my sub isDelayed($node) {
        if nqp::istype($node, QAST::Node) {
            nqp::istype($node, QAST::Block) && ($node.arity == 0);
        } else {
            nqp::die("expected a QAST::Node");
        }
    }

    my sub isVal($node) {
        if nqp::istype($node, QAST::Node) {
            nqp::istype($node, QAST::SVal) || nqp::istype($node, QAST::IVal) || nqp::istype($node, QAST::NVal);
        } else {
            nqp::die("expected a QAST::Node");
        }
    }

    my sub mkDelay($node) {
        if !nqp::istype($node, QAST::Node) {
            nqp::die("expected a QAST::Node for param 'node'");
        }
        if isVal($node) || isDelayed($node) {
            $node;
        } elsif isForced($node) {
            $node[1];
        } else {
            QAST::Stmts.new(
                mkSCall('.say', mkConcat("# calling .delayM on\n", $node.dump)),
                mkSCall('.delayM', QAST::Block.new(:arity(0), $node))
            );
        }

    }

    my sub mkImmediateOrAddAsChildTo($node, $otherwise) {
        if !nqp::istype($node, QAST::Node) {
            nqp::die("expected a QAST::Node for param 'node'");
        }
        if !nqp::istype($otherwise, QAST::Node) {
            nqp::die("expected a QAST::Node for param 'otherwise'");
        }
        if !nqp::istype($node, QAST::Var) {
            my $nVar := locVar('x');
            QAST::Block.new(
                :blocktype('immediate'),
                QAST::Op.new(:op<bind>, $nVar.declV, $node),
                mkImmediateOrAddAsChildTo($nVar, $otherwise)
            );
        } else {    # $node isa QAST::Var
            my $otherwiseWithAddedNode := nqp::clone($otherwise);
            $otherwiseWithAddedNode.push($node);
            QAST::Op.new(:op<if>,
                QAST::Op.new(:op<isstr>, $node),
                $node,
                QAST::Op.new(:op<if>,
                    QAST::Op.new(:op<isint>, $node),
                    $node,
                    QAST::Op.new(:op<if>,
                        QAST::Op.new(:op<isnum>, $node),
                        $node,
                        $otherwiseWithAddedNode
                    )
                )
            )
        }
    }

    my sub mkForce($node) {
        if nqp::istype($node, QAST::Node) {
            if isDelayed($node) {
                $node[0];
            } elsif isForced($node) || isVal($node) {
                $node;
            } else {
                my $out := mkImmediateOrAddAsChildTo(
                    $node,
                    QAST::Op.new(:op<call>)
                );
#                say(">>>> " ~ $node.dump);
#                say(">>>> " ~ $out.dump);
                $out;
            }
        } else {
            nqp::die("expected a QAST::Node");
        }
    }

    my sub mkCall($fn, *@args) {
        my $out := QAST::Op.new(:op<call>);
        if nqp::isstr($fn) {
            $out.name($fn);
        } elsif nqp::istype($fn, QAST::Node) {
            $out.push($fn);
        } else {
            nqp::die("expected a str or a QAST::Node for param 'fn'");
        }
        for @args {
            $out.push(asNode($_));
        }
        return $out;
    }

    my sub mkSCall(str $fnName, *@args) {
        if $fnName eq '.ifTag' {
            my @as := [];
            @as.push(@args.shift);
            @as.push(@args.shift);
            for @args {
                @as.push(mkDelay(asNode($_)));
            };
            mkCall($fnName, |@as);
        } else {
            mkCall($fnName, |@args);
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
        mkForce(mkSCall('.->#n', $subject, 'λ', 2));
    }

    has $!lamCount;

    my sub mkSetting() {
        my $block := QAST::Block.new(:arity(0));
        
        my $_ifTag-s := lexVar('s');    # "subject"
        my $_ifTag-x := lexVar('x');
        my $_ifTag-t := lexVar('t');
        my $_ifTag-e := lexVar('e');
        $block.push(QAST::Op.new(:op<bind>, lexVar('.ifTag', :decl<static>),
            QAST::Block.new(:arity(4),
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
            )
        ));

        my $_project-s := lexVar('s');  # "subject"
        my $_project-t := lexVar('t');  # "tag"
        my $_project-i := lexVar('i');  # "index"
        $block.push(QAST::Op.new(:op<bind>, lexVar('.->#n', :decl<static>),
            QAST::Block.new(:arity(1),
                $_project-s.declP,
                $_project-t.declP,
                $_project-i.declP,
                mkSCall('.ifTag', $_project-s, $_project-t,
                    mkListLookup($_project-s, :index($_project-i)),
                    QAST::Op.new(:op<null>)
                )
            )
        ));

        my $_strOut-p1 := lexVar('v');
        $block.push(QAST::Op.new(:op<bind>, lexVar('.strOut', :decl<static>),
            QAST::Block.new(:arity(1),
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
            )
        ));

        my $_delayM-block  := lexVar('block');
        my $_delayM-wasRun := lexVar('wasRun');
        my $_delayM-result := lexVar('result');
        $block.push(QAST::Op.new(:op<bind>, lexVar('.delayM', :decl<static>),
            QAST::Block.new(:arity(1),
                $_delayM-block.declP,
                QAST::Op.new(:op<bind>, $_delayM-wasRun.declV, asNode(0)),
                $_delayM-result.declV,
                QAST::Block.new(:arity(0),
                    QAST::Op.new(:op<if>, $_delayM-wasRun,
                        $_delayM-result,
                        QAST::Stmts.new(
                            QAST::Op.new(:op<bind>, $_delayM-wasRun, asNode(1)),
                            QAST::Op.new(:op<bind>, $_delayM-result, QAST::Op.new(:op<call>, $_delayM-block))
                        )
                    )
                )
            )
        ));

        my $_say-p1 := lexVar('v');
        $block.push(QAST::Op.new(:op<bind>, lexVar('.say', :decl<static>),
            QAST::Block.new(:arity(1),
                $_say-p1.declP,
                QAST::Op.new(:op<bind>, $_say-p1, mkForce($_say-p1)),
                QAST::Op.new(:op<say>,
                    QAST::Op.new(:op<if>,
                        QAST::Op.new(:op<isstr>, $_say-p1),
                        $_say-p1,
                        mkSCall('.strOut', $_say-p1)
                    )
                )
            )
        ));

        my $_strLit-p1 := lexVar('v');
        $block.push(QAST::Op.new(:op<bind>, lexVar('.strLit', :decl<static>),
            QAST::Block.new(:arity(1),
                $_strLit-p1.declP,
                mkConcat('"', QAST::Op.new(:op<escape>, $_strLit-p1), '"')
            )
        ));
        
        my $_apply1-f  := lexVar('f');
        my $_apply1-a1 := lexVar('a1');
        $block.push(QAST::Op.new(:op<bind>, lexVar('.apply1', :decl<static>),
            QAST::Block.new(:arity(2),
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
            )
        ));

        $block.push(QAST::Op.new(:op<bind>, lexVar('.testDelay', :decl<static>),
            mkDelay(
                QAST::Stmts.new(
                    QAST::Op.new(:op<say>, asNode('!!!!')),
                    asNode('42')
                )
            )
        ));

        return $block;
    }

    my sub match2location($match) {
        my @lines := nqp::split("\n", nqp::substr($match.orig, 0, $match.from == 0 ?? $match.chars !! $match.from));
        my $lineN := nqp::elems(@lines);
        my $colN  := 1 + nqp::chars(@lines.pop);
        my $file := $*USER_FILES;
        hash(:file($file), :line($lineN), :column($colN), :match($match));
    }

    my sub freeVars2locations(%fvs) {
        my @out := [];
        for %fvs {
            my $key := nqp::iterkey_s($_);
            my @vals := nqp::iterval($_);
            for @vals -> $val {
                if !nqp::istype($val, QUAST::Node) {
                    die("not a Node: $key => ??");
                }
                my $loc := match2location($val.node);
                $loc{'name'} := $key;
                $loc{'var'}  := $val;
                @out.push($loc);
            }
        }
        @out;
    }

    my sub loc2str(%l) {
        my $varNameStr := nqp::existskey(%l, 'var')
            ?? '  (' ~ %l<var>.name ~ ')'
            !! ''
        ;
        return '   at ' ~ %l<file> ~ ':' ~ %l<line> ~ ':' ~ %l<column> ~ $varNameStr;
    }

    my sub reportFV(str $where, $match, %fvs) {
        say(nqp::elems(%fvs), " FVs in $where @ ", '"', nqp::escape($match), '"');
        my @locs := freeVars2locations(%fvs);
        for @locs {
            say(loc2str($_));
        }
    }

    method TOP($/) {
        my $mainTermMatch := $/<termlist1orMore>;
        nqp::defor($mainTermMatch,
            nqp::die("Compile Error: no term found at all\n" ~ loc2str(match2location($/)) ~ "\n")
        );

        my $mainTerm := $mainTermMatch.ast;

        my $fvs := $mainTerm.ann('FV');
        if nqp::elems($fvs) > 0 {
            my $msg := "Compile Error: unbound variables\n";
            for freeVars2locations($fvs) {
                $msg := $msg ~ loc2str($_) ~ "\n";
            }
            nqp::die($msg);
        }

        my $s := mkSetting();
        
        $s.push(QAST::Stmts.new(:resultchild(3),
            mkSCall('.say', mkConcat(~$!lamCount, " lambdas\n------------------------------------------------")),
            #QAST::Op.new(:op<flushfh>, QAST::Op.new(:op<getstdout>)),
            
            mkSCall('.say', lexVar('.testDelay')),
            mkSCall('.say', lexVar('.testDelay')),
            
            mkSCall('.strOut', $mainTerm),
            
            mkSCall('.say', "------------------------------------------------"),
        ));
        
        make $s;
    }

    method termlist1orMore($/) {
        if nqp::elems($/<term>) == 1 {
            my $out := $/<term>[0].ast;
            #reportFV('termlist1orMore', $/, $out.ann('FV'));
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
            my $key := nqp::iterkey_s($_);
            my @vals := nqp::iterval($_);
            if nqp::existskey($fv, $key) {
                for @vals -> $val {
                    $fv{$key}.push($val);
                }
            } else {
                $fv{$key} := @vals;
            }
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
        $app.node($/);
        #reportFV('termlist2orMore', $/, $app.ann('FV'));
        make $app;
    }

    method term($/) {
        my $out := $/<t>.ast;
        #reportFV('term', $/, $out.ann('FV'));
        make $out;
    }

    method variable($/) {
        my str $name := ~$/;
        my $var := lexVar($name, :node($/));
        my $fv := hash();
        $fv{$name} := [$var];
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

        my $block := QAST::Block.new(:arity(1), :node($/), $binder, $body);

        my %fvs := nqp::clone($body.ann('FV'));
        nqp::deletekey(%fvs, $/<varName>);

        my $strRepr;
        if nqp::elems(%fvs) == 0 {
            $strRepr := asNode(~$/);
        } else {
            my %strs := hash();
            for freeVars2locations(%fvs) {
                my $k := "\n   # where " ~ $_<name> ~ ' = ';
                my $v := mkSCall('.strOut', $_<var>);
                %strs{$k} := $v;
            }
            my @strs := [~$/];
            for %strs {
                @strs.push(nqp::iterkey_s($_));
                @strs.push(nqp::iterval($_));
            }
            $strRepr := mkDelay(mkConcat(|@strs));
        }

        my $lam := QAST::Op.new(:op<list>,
            QAST::SVal.new(:value('λ')),
            $block,
            $strRepr,
        );
        $lam.annotate('FV', %fvs);
        
        $lam.annotate('id', 'λ' ~ $!lamCount);
        $!lamCount++;

        if !$body.has_ann('FV') {
            nqp::die("missing annotation 'FV' in body " ~ $/<body>);
        }
        
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
        
        my $*USER_FILES := join('; ', @a);
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
