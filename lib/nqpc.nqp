#!nqp
use nqp;
use NQPHLL;

use Util;
use Util::QAST;


# -----------------------------------------------

sub drop_takeclosure($ast) {
    nqp::die('drop_takeclosure expects a QAST::Node - got ' ~ nqp::reprname($ast) )
        unless istype($ast, QAST::Node);
    if istype($ast, QAST::Op) && $ast.op eq 'takeclosure' {
        my $child := drop_takeclosure($ast[0]);  # recurse!
        if istype($ast, QAST::SpecialArg) {
            $child.HOW.mixin($child, QAST::SpecialArg);
            $child.flat($ast.flat);
            $child.named($ast.named);
        }
        $ast := $child;
    #} elsif istype($ast, QAST::Children) {
    } elsif nqp::can($ast, 'list') { # workaround - not all nodes with children actually do that role
        my @children := [];
        for $ast.list {
            @children.push(drop_takeclosure($_));
        }
        #$ast.set_children(@children);
        my @list := $ast.list;
        while +@list { @list.pop }
        for @children { @list.push($_) }

    }
    $ast;
}

sub isinResultPosition($node, $parent) {
    my $n := nqp::elems($parent) - 1;
    if ($parent[$n] =:= $node) || (nqp::can($parent, 'resultchild') && $parent[$parent.resultchild] =:= $node) {
        return 1;
    }
    
    while --$n >= 0 {
        return 0 if $node =:= $parent[$n];
    }

    nqp::die(describe($node) ~ ' not a child of ' ~ describe($parent));
}


sub drop_bogusVars($ast, $parent = nqp::null) {
    if istype($ast, QAST::Var) && !$ast.decl {
        if istype($parent, QAST::Block, QAST::Stmt, QAST::Stmts) {
            unless isinResultPosition($ast, $parent) {
                #nqp::print(describe($parent) ~ ' ' ~ $ast.dump);
                return nqp::null;
            }
        }
    } elsif +$ast.list { # workaround - not all nodes with children actually do that role
        #say('  >> ', describe($ast), ' ', nqp::elems($ast.list));
        my @children := [];
        my $changed := 0;
        for $ast.list {
            my $child := drop_bogusVars($_, $ast);
            if nqp::isnull($child) {
                $changed := 1;
            } else {
                @children.push($child);
            }
        }
        if $changed {
            my @list := $ast.list;
            while +@list { @list.pop }
            for @children { @list.push($_) }
        }
    }
    $ast;
}


sub remove_bogusOpNames($ast) {
    nqp::die('remove_bogusOpNames expects a QAST::Node - got ' ~ nqp::reprname($ast) )
        unless istype($ast, QAST::Node);
    if istype($ast, QAST::Op) && ($ast.op ne 'call') && ($ast.op ne 'callstatic') && ($ast.op ne 'callmethod') && ($ast.op ne 'lexotic') {
        #say('>>>Op(', $ast.op, ' ', $ast.dump_extra_node_info, ')')
        #    unless nqp::index('x radix can postinc preinc add_n sub_n stringify bind bindkey concat atpos atkey die reprname defor isnull iseq_s iseq_n isgt_n islt_n isinvokable isstr isint isnum islist ishash substr if unless for while elems chars escape list hash iterkey_s iterval', $ast.op) >= 0;
        $ast.name(nqp::null_s);
    }
    for $ast.list {
        remove_bogusOpNames($_);
    }
    $ast;
}


sub remove_MAIN($ast) {
    say($ast[0].cuid);
    say("CompUnit load: \n", dump($ast.load));
    say("CompUnit main: \n", dump($ast.main));

    my @path := [];
    my $MAIN := findDef($ast, '&MAIN', @path);
    removeChild(@path[0], $MAIN);
    say(describe(@path), "\n", describe($MAIN));
    @path := [];
    my $MAINcall := findPath(-> $node, @pathUp {
            if istype($node, QAST::Op) && ($node.op eq 'call') && ($node.name eq '&MAIN' || (istype($node[0], QAST::Var) && $node[0].name eq '&MAIN')) {
                my $parent := @pathUp[0];
                if istype($parent, QAST::Op) && $parent.op eq 'if' {
                    $parent;
                } elsif istype($parent, QAST::Stmt, QAST::Stmts) {
                    $parent := @pathUp[0];
                    if istype($parent, QAST::Op) && $parent.op eq 'if' {
                        $parent;
                    } else {
                        $node
                    }
                }
            } else {
                $node.list;
            }
        },
        $ast, @path
    );
    removeChild(@path[0], $MAINcall);
    #say(describe(@path), ' ', $MAINcall.dump);
    $ast;
}



sub findDef($ast, $matcher, @pathUp = []) {
    if nqp::isstr($matcher) {
        my $name := $matcher;
        $matcher := -> $var, @pathUp { $var.name eq $name && $var.decl };
    }
    findPath(
        -> $node, @pathUp {
            my $parent := nqp::elems(@pathUp) > 0 ?? @pathUp[0] !! nqp::null;
            if nqp::isnull($parent) || istype($parent, QAST::CompUnit) {
                $node.list;
            } elsif istype($parent, QAST::Op) && istype($node, QAST::Var) {
                 $parent.op eq 'bind' && $matcher($node, @pathUp)
                    ?? $parent
                    !! nqp::null;
            } elsif istype($parent, QAST::Block, QAST::Stmts, QAST::Stmt, QAST::Op) {
                my @next := qastChildren($node, QAST::Block, QAST::Stmts, QAST::Stmt, QAST::Var, QAST::Op); # TODO: put Op nodes first
                @next;
            } else {
                0;
            }
        },
        $ast, @pathUp
    );
}

sub findDefs($ast, $matcher) {
    my @out := [];
    my $current := 1;
    while $current {
        $current := findDef($ast, -> $var, @pathUp {
            my $takeit := 0;
            if $matcher($var, @pathUp) {
                $takeit := 1;
                my $i := nqp::iterator(@out);
                while $i && $takeit {
                    $takeit := !(nqp::shift($i)[0] =:= $var);   # we're storing the parent ('bind')
                }
            }
            $takeit;
        });
        unless nqp::isnull($current) {
#            say(nqp::elems(@out), ': ', dump($current[0], :oneLine));
            @out.push($current);
        }
    }
    @out;
}

sub findValueNodeInHash($keyPredicate, $valuePredicate, $hash = NO_VALUE) is export {
    nqp::die('findValueNodeInHash expects a fn as 1st arg - got ' ~ describe($keyPredicate))
        unless nqp::isinvokable($keyPredicate);
    nqp::die('findValueNodeInHash expects a fn as 2nd arg - got ' ~ describe($valuePredicate))
        unless nqp::isinvokable($valuePredicate);
    
    if $hash =:= NO_VALUE {
        return -> $hash { findValueNodeInHash($keyPredicate, $valuePredicate, $hash) }
    } elsif !istype($hash, QAST::Node) {
        nqp::die('findValueNodeInHash expects a QAST::Node as (optional) 3rd arg - got ' ~ describe($hash));
    }
    my $found := nqp::null;
    if istype($hash, QAST::Op) && $hash.op eq 'hash' {
        my $it := nqp::iterator($hash.list);
        while $it && !$found {
            my $k := nqp::shift($it);
            if $it && $keyPredicate($k) {
                my $v := nqp::shift($it);
                if $valuePredicate($v) {
                    $found := $v;
                }
            }
        }
    }
    $found;
}

sub cloneAndSubst($node, $substitution) {
    nqp::die('cloneAndSubst expects a QAST::Node as 1st arg - got ' ~ describe($node) )
        unless istype($node, QAST::Node);
    nqp::die('cloneAndSubst expects a function as 2nd arg - got ' ~ describe($substitution) )
        unless nqp::isinvokable($substitution);
    
    #return $substitution(nqp::clone($node))    # strange: this actually prevents any recursion...!?!
    #    unless istype($node, QAST::Children);

    $node := $node.shallow_clone;   # also makes a shallow clone of the children's list
    my @children := $node.list;
    my $i := 0;
    for @children {
        my $child := cloneAndSubst($_, $substitution);
        unless nqp::isnull($child) {
            @children[$i] := $child;
            $i++;
        }
    }
    nqp::setelems(@children, $i);
    
    $substitution($node);
}


sub collect_params_and_body($node, %results = hash(:arity(0), :params({}), :stmts([]))) {
    my $arity  := %results<arity>;
    my %params := %results<params>;
    my @stmts  := %results<stmts>;
    for $node.list {
        if istype($_, QAST::Var) {
            my $varName := $_.name;
            if $_.decl {
                if $_.decl eq 'param' {
                    nqp::die("cannot handle :named parameter $varName: " ~ dump($_))
                        if $_.named;
                    nqp::die("cannot handle :slurpy parameter $varName: " ~ dump($_))
                        if $_.slurpy;
                    %params{$varName} := $arity;
                    $arity++;
                } else {
                    nqp::die('cannot handle :decl(' ~ $_.decl ~ ')');
                }
            } else {
                @stmts.push($_);
            }
        } else {
            @stmts.push($_);
        }
    }
    %results<arity> := $arity;
    %results;
}


sub inline_simple_subs($node, @inlineDefs, %inlineables = {}) {
    nqp::die('inline_simple_subs expects a QAST::Node as 1st arg - got ' ~ describe($node) )
        unless istype($node, QAST::Node);

    # on first step, prepare:
    if nqp::elems(@inlineDefs) > 0 {
        for @inlineDefs {
            next if nqp::isnull($_);
            nqp::die("invalid def of inlineable sub: " ~ describe($_))
                unless istype($_, QAST::Node);
            nqp::die("invalid def of inlineable sub: " ~ dump($_))
                unless istype($_, QAST::Op) && $_.op eq 'bind'
                    && istype($_[0], QAST::Var)
                    && istype($_[1], QAST::Block);
            my $name   := $_[0].name;
            my $block  := $_[1];
            my %results;
            if istype($block[0], QAST::Stmt, QAST::Stmts) {
                my $it := nqp::iterator($block.list);
                %results := collect_params_and_body(nqp::shift($it));
                while $it {
                    %results := collect_params_and_body(nqp::shift($it), %results);
                }
            } else {
                %results := collect_params_and_body($block);
            }
            my $arity  := %results<arity>;
            my %params := %results<params>;
            my @stmts  := %results<stmts>;


            if nqp::elems(@stmts) == 0 {
                nqp::die("no statements found in inlineable $name: " ~ dump($block));
            } elsif nqp::elems(@stmts) == 1 {
                $block := @stmts[0];
            } else {
                $block := QAST::Stmts.new(|@stmts);
            }

            %inlineables{$name} := -> @arguments {
                my $argCount := nqp::elems(@arguments);
                nqp::die("cannot inline call with $argCount args to $arity" ~ "-arity fn $name")
                    unless $argCount == $arity;
                my $out := cloneAndSubst($block, -> $n {
#                    say('####', dump($n));
                    if istype($n, QAST::Var) && nqp::existskey(%params, $n.name) {
                        my $out := @arguments[%params{$n.name}];
#                        say('#### substituted ', dump($out, :oneLine), ' for ', dump($n, :oneLine));
                        $out;
                    } else {
                        $n;
                    }
                });
                $out;
            };
        }
        return inline_simple_subs($node, [], %inlineables);
    }

    # next, recurse into children:
    my $i := 0;
    my @children := $node.list;
    for @children {
        @children[$i] := inline_simple_subs($_, [], %inlineables);
        $i++;
    }

    if istype($node, QAST::Op) && ($node.op eq 'call' || $node.op eq 'callstatic') {
        my $codeMaker := %inlineables{$node.name};
        if $codeMaker {
            my $out := $codeMaker($node.list);
#            say('>>>> inlined ', dump($out), "\n>>>> for ", dump($node));
            $out.node($node.node);
            $out.flat($node.flat);
            $out.named($node.named);
            $node := $out;
        }
    }
    
    $node;
}

sub inline_simple_methods($node) {
    nqp::die('inline_simple_methods expects a QAST::Node - got ' ~ describe($node) )
        unless istype($node, QAST::Node);

    # first, recurse:
    for $node.list {
        inline_simple_methods($_);
    }

    if istype($node, QAST::Op) && $node.op eq 'callmethod' {
        my $meth := $node.name;
        if $meth {
            if nqp::index('push pop shift unshift', $meth) > -1 {
                $node.op($meth);
                $node.name(nqp::null_s);
            } elsif $meth eq 'key' {
                $node.op('iterkey_s');
                $node.name(nqp::null_s);
            } elsif $meth eq 'value' {
                $node.op('iterval');
                $node.name(nqp::null_s);
            }
        }
    }
    
    $node;
}

sub replace_assoc_and_pos_scoped($node) {
    nqp::die('replace_assoc_and_pos_scoped expects a QAST::Node - got ' ~ describe($node) )
        unless istype($node, QAST::Node);

    # first, recurse:
    my $i := 0;
    my @children := $node.list;
    for @children {
        @children[$i] := replace_assoc_and_pos_scoped($_);
        $i++;
    }

    if istype($node, QAST::Op) && ($node.op eq 'bind') && !istype($node[0], QAST::Var) {
        # then our 1st child was just transformed to an 'atkey' or 'atpos'
        my $child1 := $node.shift;
        nqp::die("ooops: " ~ dump($child1, :oneLine))
            unless istype($child1, QAST::Op);
        my $which := nqp::substr($child1.op, 0, 5); # substr to allow for typed variants _i, _s, etc
        nqp::die("ooops: cannot handle op $which: " ~ dump($child1, :oneLine))
            unless $which eq 'atpos' || $which eq 'atkey';
        $node.op('bind' ~ nqp::substr($child1.op, 2));
        $node.node($child1.node);
        $node.flat($child1.flat);
        $node.named($child1.named);
        $node.unshift($child1[1]);
        $node.unshift($child1[0]);
    } elsif istype($node, QAST::VarWithFallback) {
        my $fallback := $node.fallback;
        if nqp::isnull($fallback) || istype($fallback, NQPMu) {
            $fallback := nqp::null;
        } else {
            nqp::die('cannot handle fallback ' ~ describe($node.fallback))
        }
        my $scope := $node.scope;
        my $op;
        if $scope eq 'positional' {
            $op := 'atpos';
        } elsif $scope eq 'associative' {
            $op := 'atkey';
        }
        if $op {
            $node := QAST::Op.new(:$op,
                :node($node.node),
                :named($node.named),
                :flat($node.flat),
                |$node.list
            );
            #$node := $out;
        }
    }
    $node;
}


sub renameVars($ast, $map) {
    nqp::die('renameVars expects a QAST::Node as 1st arg - got ' ~ describe($ast) )
        unless istype($ast, QAST::Node);
    nqp::die('renameVars expects a unary fn as 2nd arg(optional) - got ' ~ describe($map) )
        unless nqp::isinvokable($map);

    if istype($ast, QAST::Var) 
       || (
          istype($ast, QAST::Op)
          && (($ast.op eq 'call') || ($ast.op eq 'callstatic'))
        ) {
        my str $old := $ast.name;
        my str $new := $map($old);
        if $new ne $old {
            $ast.name($new);
        }
    }
    #if istype($ast, QAST::Children) {
    for $ast.list {
        renameVars($_, $map);
    }
    $ast;
}

# -----------------------------------------------



class SmartCompiler is NQP::Compiler {

    # Where to search for user source files.
    # Must use forward slash '/' as dir separator & must NOT end in one!
    has @!user_srcpaths;

    has $!user_binname;

    method BUILD() {
        # in this order (!):
        self.addstage('ast_save',           :after<ast>);
        self.addstage('fix_var_attrs',      :after<ast>);
        #self.addstage('optimize',           :before<ast_save>);

        # Add extra command line options.
        my @clo := self.commandline_options();
        @clo.push('parsetrace');
        @clo.push('setting=s');
        @clo.push('setting-path=s');
        @clo.push('module-path=s');
        @clo.push('no-regex-lib');
        @clo.push('stable-sc');
        @clo.push('optimize=s');

        # XXX don't hard-code this!
        @!user_srcpaths := <. lib lib/L>;
    }

    # called "user-progname" (with a dash instead of an underscore) in HLL::Compiler
    # which doesn't fit well with "compiler_progname"
    method user_progname() {
        self.user-progname();
    }

    method user_binname($v = NO_VALUE) {
        $!user_binname := $v unless $v =:= NO_VALUE;
        $!user_binname;
    }

    method user_srcpaths() {
        @!user_srcpaths;
    }

    method log($msg, *@moreMsgPieces) {
        my str $out := '# [' ~ self.compiler_progname ~ '] ' ~ $msg;
        for @moreMsgPieces {
            $out := $out ~ $_;
        }
        say($out);
    }

    method find_file($module_name, @search_paths, :$ext!) {
        my $path;
        my $file_name := nqp::join('/', nqp::split('::', $module_name)) ~ ".$ext";
        for @search_paths {
            $path := "$_/$file_name";
            last if nqp::stat($path, nqp::const::STAT_EXISTS)
                 #&& nqp::filereadable($path)
            ;
            $path := nqp::null;
        }
        $path;
    }

    method find_src(str $module_name, :$ext!) {
        self.find_file($module_name, @!user_srcpaths, :$ext);
    }
    
    method find_bytecode($module_name, :$ext!, :$with-nqplib) {
            my $loader := nqp::getcurhllsym('ModuleLoader');
            my @module_paths := $loader.search_path('module-path'); # path from opt --module-path=s, if any
            if $with-nqplib {
                @module_paths.unshift(nqp::backendconfig()<prefix> ~ '/languages/nqp/lib');
            }
            self.find_file($module_name, @module_paths, :$ext);
    }

    method compileDependency(str $module_name, @on_behalf) {
        my $out;
        my $src_path := self.find_src($module_name, :ext<nqp>);
        if $src_path {
            my $bc_path := self.find_bytecode($module_name, :ext<moarvm>);
            if $bc_path {
                my $src_time := nqp::stat($src_path, nqp::const::STAT_MODIFYTIME);
                my $bc_time  := nqp::stat($bc_path,  nqp::const::STAT_MODIFYTIME);
                if $src_time < $bc_time {
                    return $bc_path; # up-to-date, no need to recompile
                }
            }
            my $clone := nqp::clone(self);
            return $clone.compileFile($src_path, :target<mbc>);

        } else { # no src file, so maybe it's a module from the NQP language directory?
            return self.find_bytecode($module_name, :ext<moarvm>, :with-nqplib);
        }
    }

    method collect_stats($node) {
        my %results := {};
        my sub doit($node) {
            nqp::die("collect_stats expects a QAST::Node - got " ~ describe($node))
                unless istype($node, QAST::Node);

            my $HOWname := $node.HOW.name($node);
    #        %results{$HOWname}++;

            %results<Node>++; # size of tree
            if istype($node, QAST::Block) {
                %results<Block>++;
            } elsif istype($node, QAST::Stmt, QAST::Stmts) {
                %results<Stmt(s)>++;
            } elsif istype($node, QAST::Op) {
                my $op := $node.op;
    #            %results{$HOWname ~ '(' ~ $op ~ ')'}++;
                %results<op>++;
                %results<list>++        if  $op eq 'list';
                %results<hash>++        if  $op eq 'hash';
                %results<bind>++        if  $op eq 'bind';
                %results<call>++        if  $op eq 'call';
                %results<callstatic>++  if  $op eq 'callstatic';
                %results<callmethod>++  if  $op eq 'callmethod';
                %results<takeclosure>++ if  $op eq 'takeclosure';
            } elsif istype($node, QAST::Var) {
                %results<Var>++;
            } elsif istype($node, QAST::IVal) {
                %results<IVal>++;
            } elsif istype($node, QAST::NVal) {
                %results<NVal>++;
            } elsif istype($node, QAST::SVal) {
                %results<SVal>++;
                %results<SValChars> := %results<SValChars> + nqp::chars($node.value);
            }

            for $node.list {
                doit($_);
            }
        }
        doit($node);
        %results<callish> := %results<call> + %results<callstatic> + %results<callmethod>;
        %results<val> := %results<IVal> + %results<NVal> + %results<SVal>;
        %results;
    }

    # override stage 'ast' and make the AST stringifiable
    
    method ast($source, *%adverbs) {
        my $ast := $source.ast();
        self.panic("Unable to obtain AST from " ~ $source.HOW.name($source))
            unless $ast ~~ QAST::Node;
        $ast.HOW.mixin($ast, StrByDump);
        $ast;
    }

    # additional stages

    method fix_var_attrs($ast) {
        fix_var_attrs($ast);
    }

    method ast_clean($ast, *%adverbs) {
        self.log('ast_clean: ', self.user-progname, '...');
        
        $ast := drop_takeclosure($ast);
        
        $ast := drop_Stmts($ast);
        $ast := drop_bogusVars($ast);       # do this *after* drop_Stmts !!!
        $ast := remove_bogusOpNames($ast);
        #$ast := remove_MAIN($ast);
        
        # from here it's rather optimization...
        $ast := replace_assoc_and_pos_scoped($ast);
        $ast := inline_simple_methods($ast);

        my @inlinecandidates;
        @inlinecandidates := findDefs($ast, -> $var, @pathUp {
               (nqp::index($var.name, '&STATS_') > -1)
            || (nqp::index($var.name, '&LAMFIELD_') > -1)
            || (nqp::index('&lam2id &lam2code &lam2fvs &int2str &num2str', $var.name) > -1)
        });
        $ast := inline_simple_subs($ast, @inlinecandidates);

        #$ast := renameVars($ast, -> $s {
        #    my str $fst := nqp::substr($s, 0, 1);
        #    my str $snd := nqp::substr($s, 1, 1);
        #    $fst eq '&' || $snd eq 'λ'
        #        ??  '.' ~ nqp::substr($s, 1)
        #        !! $s;
        #});

        $ast;
    }

    method ast_stats($ast, *%adverbs) {
        my %stats := self.collect_stats($ast);

        my @statskeyDefs := findDefs($ast, -> $var, @pathUp {
            nqp::index($var.name, 'STATS_') > -1;
        });
        my @statskeys := [];
        for @statskeyDefs {
            my $v := $_[1][0];
            if istype($v, QAST::SVal, QAST::IVal, QAST::NVal) {
                 @statskeys.push($v.value);
            }
        }

        my sub svalPred($value = NO_VALUE) {
            -> $node { istype($node, QAST::SVal) && ($value =:= NO_VALUE || $node.value eq $value) }
        }

        my sub ivalPred($value = NO_VALUE) {
            -> $node { istype($node, QAST::IVal) && ($value =:= NO_VALUE || $node.value == $value) }
        }

        my sub opPred($op = NO_VALUE) {
            -> $node { istype($node, QAST::Op) && ($op =:= NO_VALUE || $node.op eq $op) }
        }
        

        my $findStatsHash := findValueNodeInHash(svalPred('stats'), opPred('hash'));
        my $infoHashDef := findDef($ast, -> $var, @pathUp {
            if $var.name eq '%info' {
                $findStatsHash(@pathUp[0][1]);
            }
        });
        my $infoHash := $findStatsHash($infoHashDef[1]);
        say('>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>' ~ istype($infoHash, QAST::Op));
        if istype($infoHash, QAST::Op) && ($infoHash.op eq 'hash') {
            my $findStatNode := -> $statKey {
                findValueNodeInHash(svalPred($statKey), ivalPred(), $infoHash)
            };
            for @statskeys {
                my $node := $findStatNode($_);
                if $node && nqp::existskey(%stats, $_) {
                    $node.value(%stats{$_});
#                    say(">>>> stat $_ := ", dump($node, :oneLine));
                }
            }
            say(dump($infoHashDef));
        } else {
            self.log('ast_stats WARNING: no %info hash found in AST of ', self.user-progname);
            self.log('ast_stats WARNING: ...dunno how to insert actual stats - which are:');
            for %stats {
                self.log('    ', nqp::iterkey_s($_), ' = ', nqp::iterval($_))
            }
        }

        $ast;
    }

    method ast_save($ast, *%adverbs) {
        my $qastfileName := self.user-progname ~ '.qast';
        return $ast
            if %adverbs<output> eq $qastfileName;
        spew($qastfileName, ~$ast);
        #self.log('ast_save: QAST dump written to ', $qastfileName);
        $ast;
    }

    method write_bytecode($mast, *%adverbs) {
        #self.log('write_bytecode: adverbs=' ~ describe(%adverbs));
        if %adverbs<target> eq 'mbc' && %adverbs<output> {
            self.log('write_bytecode: omitted because of'
                ~ ' :target("' ~ %adverbs<target> ~ '")'
                ~ ' and :output("' ~ %adverbs<output> ~ '")'
            );
        } else {
            my $assmbler := nqp::getcomp('MAST');
            $assmbler.assemble_to_file($mast, self.user_binname);
            self.log('write_bytecode: ' ~ describe($mast) ~ ' ~> ' ~ self.user_binname);
        }
        $mast;
    }

}

class NQPActions is NQP::Actions {
    
    method statement_control:sym<use>($/) {
        my $out;

        my @expPathUp := [];
        my $export := findPath(-> $node, @pathUp {
            istype($node, QAST::Var) && ($node.name eq 'EXPORT') && $node.decl eq 'static'
                || $node.list;
        }, $*UNIT, @expPathUp);

        if $export {
            my $deps := findPath(-> $node, @pathUp {
                if (+@pathUp > 1) && @pathUp[1] =:= @expPathUp[0] {
                    my $parent := @pathUp[0];
                    my $brother := $parent[0];
                    istype($node, QAST::Op) && $node.op eq 'list'
                        && istype($parent, QAST::Op) && $parent.op eq 'bind'
                        && istype($brother, QAST::Var) && ($brother.name eq '@?DEPENDENCIES')
                        || $node.list;
                } else {
                    $node.list
                }
            }, $*UNIT);

            

            unless $deps {
                $deps := QAST::Op.new(:op<list>);
                my $depsBinding := QAST::Op.new(:op<bind>,
                    QAST::Var.new(
                        :name('@?DEPENDENCIES'),
                        :scope<lexical>,
                        :decl<static>,
                    ),
                    $deps
                );
                @expPathUp[0].push($depsBinding);
                #say(dump(@expPathUp[0]));
            }

            $deps.push(QAST::SVal.new(:value($/<name>), :node($/)));

            $*COMPILER.log($*COMPILER.user_progname, ' dependency: "' ~ $/<name> ~ '"');
            my $depOut := $*COMPILER.compileDependency(~$/<name>, []);
            #say('>>>>>> ' ~ describe($depOut));
        }

        my $super := nqp::findmethod(self.HOW.mro(self)[1], 'statement_control:sym<use>');
        $out := $super(self, $/);
        #$out := QAST::Stmts.new();

        #my $glob := findPath(-> $node, @pathUp {
        #    istype($node, QAST::Var) && ($node.name eq 'GLOBALish')
        #        || $node.list;
        #}, $*UNIT);
        #say('>>>>>> ', dump($glob));
        #say('>>>>>> ', describe(nqp::who($glob.default)));
        
        $out.node($/);
        $out.annotate('use', ~$/<name>);
        #say(dump($out));
        make $out;
    }
}



my $needsCompilation := 0;

class NQPCompiler is SmartCompiler {

    method BUILD() {
        self.language('nqp');
        self.parsegrammar(NQP::Grammar);
        self.parseactions(NQPActions);
        return self;
    }

    method parse($source, *%adverbs) {
        my $*COMPILER := self;
        my $parse := nqp::findmethod(self.HOW.mro(self)[1], 'parse');
        $parse(self, $source, |%adverbs);
    }
    

    method compiler_progname($value = NO_VALUE) { 'nqpc' }

    method handle-exception($error) {
        nqp::rethrow($error);
    }

    method compileFile($src_path, :$target = 'mbc', :$stagestats) {
        # replace all backslashes with slashes
        $src_path := nqp::join('/', nqp::split('\\', $src_path));
        if !nqp::filereadable($src_path) {
            #self.panic("no such file: $src_path");
        }
        # strip off working dir prefix from $src_path, if any
        my $cwd := nqp::join('/', nqp::split('\\', nqp::cwd));
        if nqp::index($src_path, $cwd) == 0 {
            $src_path := nqp::substr($src_path, nqp::chars($cwd) + 1);
        }
        # strip off './' prefix from $src_path, if any
        if nqp::index($src_path, './') == 0 {
            $src_path := nqp::substr($src_path, 2);
        }

        my $l := nqp::chars($src_path);
        
        # source file extension (without the dot)
        my $x := nqp::rindex($src_path, '.');
        if $x <= 0 {    # yes, also files like ".gitignore", for example
            self.panic("invalid source file (no extension): $src_path");
        }
        my $src_ext := nqp::substr($src_path, $x + 1);
        
        # source file name (without path prefix and extension)
        my $i := nqp::rindex($src_path, '/');
        my $src_name := nqp::substr($src_path, $i + 1, $x - $i - 1);
        
        # $src_dir will contain the relative path from $cwd 
        # to (the folder representing) $src_lib, which in turn contains $src_name.$src_ext
        my $src_dir := nqp::substr($src_path, 0, max(0, $i));
        my $src_lib := '';
        # strip off any user_srcpath prefix
        for self.user_srcpaths {
            if nqp::index($src_dir, $_) == 0 {
                $src_lib := nqp::substr($src_dir, nqp::chars($_) + 1);
                $src_dir := $_;
                last;
            }
        }
        unless $src_dir {
            $src_dir := '.';
        }
        my $vm_ext  := 'moarvm';
        my $vm_dir  := 'blib';
        my $vm_path;
        if $src_lib {
            $src_path := "$src_dir/$src_lib/$src_name.$src_ext";
            $vm_path := "$vm_dir/$src_lib/$src_name.$vm_ext";
            #$src_lib := nqp::join('::', nqp::split('/', $src_lib));
        } else {
            $src_path := "$src_dir/$src_name.$src_ext";
            $vm_path := "$vm_dir/$src_name.$vm_ext";
        }
        self.user_binname($vm_path);

        my $ast_path := "$src_path.qast";

#        nqp::say(describe(hash(:$src_path, :$src_dir, :$src_lib, :$vm_path, :$src_name, :$src_ext, :$ast_path)));



        $needsCompilation := 1; #$needsCompilation || ($nqpTime > $mvmTime);
        if !$needsCompilation {
            return nqp::null;   # means: "not compiled (again) because it was up-to-date"
        } else {
            my @opts := [
                #'--module-path=L',
            ];
            @opts.push("--target=$target") if $target;

            if $target eq 'mbc' {
                if nqp::stat($vm_path, nqp::const::STAT_EXISTS) && !nqp::filewritable($vm_path) {
                    nqp::die("cannot write to file: $vm_path");
                }
                @opts.push('--output=' ~ $vm_path);
            } elsif $target eq 'ast' || $target eq 'ast_clean' || $target eq 'ast_save' {
                @opts.push('--output=' ~ $ast_path);    # not only write it but also prevent NQP::Compiler to dump it to stdout and return a null
            }
            my @args := nqp::clone(@opts);
            @args.unshift('nqpc');  # give it a program name (for command_line)
            @args.push($src_path);
            #say($vm_path, '...');

            self.log('$ ', nqp::join(' ', @args));
            #say(nqp::x('-', 29));
            my $*USER_FILE := $src_path;
            my $result;
            my $error;
            try {
                $result := self.command_line(@args, 
                    :encoding('utf8'), 
                    :transcode('ascii iso-8859-1'),
                    :$stagestats
                );
                CATCH {
                    $error := $_;
                }
            }
            unless $error {
                if nqp::isnull($result) {   # returning non-null means: "yes, we did compile and write it to disk"
                    if $target eq 'mbc' {
                        $result := $vm_path;
                    } else {
                        nqp::die("??? - successfully compiled $src_path to target $target - but got null result...!?");
                    }
                }
                return $result;
            }
            
            my $msg := nqp::getmessage($error);
            my $msglc := nqp::lc($msg);
            my $from;
            my $to;
            if nqp::index($msglc, 'no such file') > -1 {
                $from := nqp::index($msglc, '\'') + 1;
                $to   := nqp::index($msglc, '\'', $from);
                my $file := nqp::substr($msg, $from, $to - $from);
                say('Error: missing module "', $file ~ '" (original error: "' ~ nqp::escape($msg) ~ '")');
            } elsif nqp::index($msglc, 'unable to write bytecode') > -1 {
                $from := nqp::index($msglc, '\'') + 1;
                $to   := nqp::index($msglc, '\'', $from);
                my $file := nqp::substr($msg, $from, $to - $from);
                my $line := 1;
                $msg := nqp::join('', [
                          'Error: ', $msg,
                    "\n", '  at ', $src_path, ':', ~$line,
                    "\n"
                ]);
            } elsif nqp::index($msglc, 'confused') > -1 {
                $from := nqp::index($msglc, 'at line') + 1;
                $from := nqp::findcclass(nqp::const::CCLASS_NUMERIC, $msglc, $from, nqp::chars($msglc) - $from);
                $to   := nqp::findnotcclass(nqp::const::CCLASS_NUMERIC, $msglc, $from, nqp::chars($msglc) - $from);
                my $line := nqp::substr($msg, $from, $to - $from);
                $line := max(1, $line - 1);
                $msg := nqp::substr($msg, 0, $from) ~ $line ~ nqp::substr($msg, $to);
                $msg := nqp::join('', [
                          'Error: ', $msg,
                    "\n", '  at ', $src_path, ':', ~$line,
                    "\n"
                ]);
            } elsif nqp::index($msglc, 'assignment ("=") not supported ') > -1 {
                $from := nqp::index($msglc, 'at line') + 1;
                $from := nqp::findcclass(nqp::const::CCLASS_NUMERIC, $msglc, $from, nqp::chars($msglc) - $from);
                $to   := nqp::findnotcclass(nqp::const::CCLASS_NUMERIC, $msglc, $from, nqp::chars($msglc) - $from);
                my $line := nqp::substr($msg, $from, $to - $from);
                $line := max(1, $line - 1);
                my @lines := linesFrom($src_path, $line, 2);
                my $i := 0;
                my $n := nqp::elems(@lines);
                my $column;
                while $i < $n {
                    my $line := @lines[$i];
                    my $at := nqp::index($line, '=');
                    if $at > -1 {
                        $column := $at + 1;
                        $i := $n;   # exit loop
                    } else {
                        $i++;
                        $line++;
                    }
                }
                $msg := nqp::substr($msg, 0, $from) ~ $line ~ nqp::substr($msg, $to);
                $msg := nqp::join('', [
                          'Error: ', $msg,
                    "\n", '   at ', $src_path, ':', ~$line, ($column ?? ':' ~ $column !! ''),
                    "\n",
               ]);
            # TODO: Unable to parse expression in blockoid; couldn't find final '}'  at line 143, near "$msg := $m"
            # TODO: Use of undeclared variable '$fuck' at line 4, near " := [a b];"
            # TODO: Malformed binding at line 4, near "[a b];\ngra"
            } elsif 0 {
                my $line := 1;
                my $column;
                $msg := nqp::join('', [
                          'ERROR: ', $msg,
                    "\n", '   at ', $src_path, ':', ~$line, ($column ?? ':' ~ $column !! ''),
                    "\n",
               ]);
            } else {
                $msg := $msg ~ nqp::join("\n", nqp::backtracestrings($error));
            }
            nqp::flushfh(nqp::getstdout());
            nqp::die($msg);
        }
    }

}


sub flatten($args) {
    return [$args]
        unless nqp::islist($args);
    my @out := [];
    for $args -> $_ {
        if nqp::islist($_) {
            for flatten($_) -> $_ {
                @out.push($_);
            }
        } else {
            @out.push($_);
        }
    }
    @out;
}




sub MAIN(*@ARGS) {
    @ARGS := flatten(@ARGS);

    my $cwd := nqp::cwd();
    my $sep := nqp::x('-', 29);
    my $nqpc := NQPCompiler.new();
    my %opts := hash();
    #say('CWD=', describe($cwd), "\n@ARGS=", describe(@ARGS));
    
    #nqp::exit(0);

    @ARGS.shift;  # first is program name

    if nqp::elems(@ARGS) == 0 {
        #@ARGS.push('L/LGrammar.nqp');
        #@ARGS.push('L/LActions.nqp');
        #@ARGS.push('L/L.nqp');

        @ARGS.push('lib/L/runtime.nqp');
        ##$nqpc.addstage('ast_clean', :before<ast_save>);
        #$nqpc.addstage('ast_stats', :before<ast_save>);
        #%opts<stagestats> := 1;
        #%opts<target>     := '';    # ...and run it
    }
        #%opts<stagestats> := 1;
        $nqpc.addstage('write_bytecode', :before<mbc>);


    for @ARGS {
        my $file := $_;
        
        my $result := $nqpc.compileFile($file, |%opts);
        #my $result := $nqpc.compileFile("$cwd/./nqpc.nqp", |%opts);
        #my $result := $nqpc.compileFile("$cwd/lib/testing.nqp", |%opts);
        #my $result := $nqpc.compileFile("$cwd/./lib/testing.nqp", |%opts);
        #my $result := $nqpc.compileFile("$cwd/lib/L/runtime.nqp", |%opts);

        if nqp::isnull($result) {
            $nqpc.log("uptodate: $file");
        } else {
            $nqpc.log("compiled: $file ~> " ~ describe($result));
        }
        CATCH {
            $nqpc.log("ERROR: $file");
            $nqpc.log($sep);
            $nqpc.log("  CWD: $cwd");
            $nqpc.log(' ARGS: ', nqp::join(' ', @ARGS));
            $nqpc.log('');
            $nqpc.log(~$_);
            nqp::exit(1);
            
            #nqp::die($msg);    # cannot do this: sometimes "Memory allocation failed; could not allocate zu bytes"
        }
    }
    say($sep);
}

