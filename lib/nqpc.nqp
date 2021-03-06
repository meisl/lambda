#!nqp
use nqp;
use NQPHLL;

use Util;
use Util::QAST;


my class NO_VALUE {}


# -----------------------------------------------


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


sub drop_bogusVars($ast) {
    insist-isa($ast, QAST::CompUnit);
    my $block := $ast[0];
    insist-isa($block, QAST::Block);
    my @children := $block.list;
    if +@children {
        my $last := @children[+@children - 1];
        TreeWalk.dfs-up(
            -> $n, @p {
                if $n =:= $block {
                    TreeWalkDo.recurse
                } else {
                    #say('>>>>>' ~ dump($n, :oneLine));
                    TreeWalkDo.return(:take(
                        !($n =:= $last) && isVar($n) && !$n.decl
                    ));
                }
            },
            -> $n, @p { TreeWalk.remove },
            $block
        );
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


# -----------------------------------------------



class SmartCompiler is NQP::Compiler {

    # Where to search for user source files.
    # Must use forward slash '/' as dir separator & must NOT end in one!
    has @!user_srcpaths;

    has $!user_binname;
    has $!log_level;
    has %!interactive_commands;

    method BUILD() {
        # in this order (!):
        self.addstage('ast_save',           :after<ast>);
        self.addstage('ast_clean',          :before<ast_save>);
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
        $!log_level := 'WARN';
        %!interactive_commands := {};
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

    method log_level($level = NO_VALUE) {
        $!log_level := $level unless $level =:= NO_VALUE;
        $!log_level;
    }
    

    method log($msg, *@moreMsgPieces, :$level = 'INFO') {
        if self.log_level eq 'INFO' 
            || self.log_level eq 'WARN' && ($level ne 'INFO')
            || self.log_level eq 'ERROR' && ($level eq 'ERROR')
        {
            my str $out := '# [' ~ self.compiler_progname ~ "|$level] " ~ $msg;
            for @moreMsgPieces {
                $out := $out ~ $_;
            }
            say($out);
        }
    }

    method backend() {
        nqp::getattr(self, HLL::Compiler, '$!backend');
    }

    method version_string() {
        self.language ~ ' v' ~ self.config<version>;
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

    method interactive_command(str $name, $code = NO_VALUE) {
        if $code =:= NO_VALUE {
            %!interactive_commands{$name};
        } else {
            my &code := $code;   # check if it's invokable
            %!interactive_commands{$name} := &code;
        }
    }
    

    method readline($in, $out, $prompt) {
        nqp::printfh($out, $prompt);
        my $line := trim(nqp::readlinefh($in));
        my $cmd := self.interactive_command($line);
        if $cmd {
            $cmd(:$in, :$out);
            '';
        } else {
            $line;
        }
    }

    method autoprint($value, $stdout?) {
        #say('$*AUTOPRINTPOS: ' ~ $*AUTOPRINTPOS);
        #say('nqp::tellfh(nqp::getstdout()): ' ~ nqp::tellfh(nqp::getstdout()));
        nqp::sayfh($stdout // nqp::getstdout(), $value);
    }

    method collect_stats($node) {
        my %results := {};
        my sub doit($node) {
            nqp::die("collect_stats expects a QAST::Node - got " ~ describe($node))
                unless istype($node, QAST::Node);

            my $HOWname := howName($node);
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
        self.panic("Unable to obtain AST from " ~ howName($source))
            unless $ast ~~ QAST::Node;
        $ast.HOW.mixin($ast, StrByDump);
        self.log('ast: ', self.user-progname, ' done.');
        $ast;
    }

    # additional stages

    method ast_clean($ast, *%adverbs) {
        self.log('ast_clean: ', self.user-progname, '...');
        
        $ast := fix_var_attrs($ast);
        $ast := drop_takeclosure($ast);
        $ast := drop_Stmts($ast);
        self.log('ast_clean: ', self.user-progname, ' / drop_Stmts done.');
        
        $ast := drop_bogusVars($ast);       # do this *after* drop_Stmts !!!
        $ast := remove_bogusOpNames($ast);
        #$ast := remove_MAIN($ast);
        
        # from here it's rather optimization...
        $ast := replace_assoc_and_pos_scoped($ast);
        $ast := inline_simple_methods($ast);

        #$ast := renameVars($ast, -> $s {
        #    my str $fst := nqp::substr($s, 0, 1);
        #    my str $snd := nqp::substr($s, 1, 1);
        #    $fst eq '&' || $snd eq 'λ'
        #        ??  '.' ~ nqp::substr($s, 1)
        #        !! $s;
        #});

        $ast;
    }

    method inline_subs($ast, *%adverbs) {
        my @inlinecandidates := [];
        TreeWalk.dfs-up(
            -> $n, @a {
                TreeWalkDo.recurse(:take(istype($n, QAST::Op) && ($n.op eq 'bind')
                    && istype($n[0], QAST::Var) && (nqp::index($n[0].name, '&') == 0)
                    && (($n[0].decl eq 'var') || ($n[0].decl eq 'static') )
                    && istype($n[1], QAST::Block)
                    
                ));
            },
            -> $n, @a {
                my $name := $n[0].name;
                my %subDesc := collect_params_and_body($n[1], :$name);
                unless %subDesc<locals> || %subDesc<slurpy> || %subDesc<named> || %subDesc<optional>
                    || %subDesc<recursive>  # do NOT try to inline recursive functions!
                    || istype(%subDesc<body>, QAST::Block, QAST::Stmts, QAST::Stmt)
                {
                    @inlinecandidates.push($n);
                    #TreeWalk.remove if nqp::uc($name) eq $name;   # ATTENTION: renders ast_stats dysfunctional
                }
            },
            $ast
        );

        self.log('inline_subs: ', 'candidate ', $_[0].name) for @inlinecandidates;
        $ast := inline_simple_subs($ast, @inlinecandidates);
        
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

        if istype($infoHash, QAST::Op) && ($infoHash.op eq 'hash') {
            my $findStatNode := -> $statKey {
                findValueNodeInHash(svalPred($statKey), ivalPred(), $infoHash)
            };
            for @statskeys {
                my $node := $findStatNode($_);
                if $node && nqp::existskey(%stats, $_) {
                    $node.value(%stats{$_});
                }
            }
            self.log('ast_stats: ', dump($infoHashDef, :oneLine));
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
        self.log('ast_save: QAST dump written to ', $qastfileName);
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

        $out := super(self, 'statement_control:sym<use>', $/);

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
        self.log('parse: ', self.user-progname, '...');
        my $*COMPILER := self;
        my $out := super(self, 'parse', $source, |%adverbs);
        self.log('parse: ', self.user-progname, ' done.');
        $out;
    }
    

    method compiler_progname($value = NO_VALUE) { 'nqpc' }

    method handle-exception($error) {
        nqp::rethrow($error);
    }

    method compileFile($src_path, :$target = 'mbc', :$stagestats, *%adverbs) {
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





sub MAIN(*@ARGS) {
    @ARGS := flatten(@ARGS);

    my $cwd := nqp::cwd();
    my $sep := nqp::x('-', 29);
    my $nqpc := NQPCompiler.new();
    my %opts := hash();
    
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
    $nqpc.log_level('INFO');

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
            $nqpc.log(:level<ERROR>, " FILE: $file");
            $nqpc.log(:level<ERROR>, "  CWD: $cwd");
            $nqpc.log(:level<ERROR>, ' ARGS: ', nqp::join(' ', @ARGS));
            $nqpc.log(:level<ERROR>, '');
            $nqpc.log(:level<ERROR>, ~$_);
            nqp::exit(1);
            
            #nqp::die($msg);    # cannot do this: sometimes "Memory allocation failed; could not allocate zu bytes"
        }
    }
    say($sep);
}

