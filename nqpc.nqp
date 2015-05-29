use nqp;
use NQPHLL;


sub max($a, $b) is export { $a > $b ?? $a !! $b }
sub min($a, $b) is export { $a < $b ?? $a !! $b }

sub whatsit($v) is export {
    my $reprname := nqp::reprname($v);

    if nqp::isstr($v) {
        my $length := nqp::chars($v);
        if $length > 80 {
            return '"' ~ nqp::escape(nqp::substr($v, 0, 45)) ~ '"'
                 ~ ' ~ ... ~ '
                 ~ '"' ~ nqp::escape(nqp::substr($v, $length - 25)) ~ '"'
           ;
        } else {
            return '"' ~ nqp::escape($v) ~ '"';
        }
    } elsif nqp::isint($v) || nqp::isnum($v) {
        return $reprname ~ ' ' ~ $v;
    } elsif nqp::ishash($v) {
        my @kvs := [];
        for $v {
            my $k := nqp::iterkey_s($_);
            my $v := nqp::iterval($_);
            @kvs.push(":$k(" ~ whatsit($v) ~ ')');
        }
        return 'hash(' ~ nqp::join(', ', @kvs) ~ ')';
    } elsif nqp::islist($v) {
        my @out := [];
        for $v {
            @out.push(whatsit($_));
        }
        return '[' ~ nqp::join(', ', @out) ~ ']';
    } elsif nqp::istype($v, QAST::Node) {
        my $s := $v.HOW.name($v);
        my $x := $v.dump_extra_node_info;
        return $x ?? "$s($x)" !! $s;
    #} elsif nqp::istype($v, Something) { ??? }
    } elsif nqp::can($v.HOW, 'name') {
        return $v.HOW.name($v);
    } else {
        return $reprname
    }
}

sub linesFrom(str $filename, $from = 1, $count?) is export {
    my $to := $from + nqp::defor($count, nqp::inf());
    my @out := [];
    my $fh := nqp::open($filename, 'r');
    nqp::setinputlinesep($fh, "\n");
    my $linesRead := 0;
    while !nqp::eoffh($fh) && ($linesRead < $to) {
        my $line := nqp::readlinefh($fh);
        $linesRead++;
        @out.push($line) unless $linesRead < $from;
    }
    nqp::closefh($fh);
    @out;
}

# -----------------------------------------------


sub dump($node, $indent = '', :$isLastChild = 2, :$isBlockChild = 0) {
    my $clsStr := nqp::substr($node.HOW.name($node), 6);
    my $nodesNodeStr := '';
    if $node.node {
        $nodesNodeStr := nqp::escape(~$node.node);
        if nqp::chars($nodesNodeStr) > 54 {
            $nodesNodeStr := nqp::substr($nodesNodeStr, 0, 51) ~ '"...'
        } else {
            $nodesNodeStr := $nodesNodeStr ~ '"';
        }
        $nodesNodeStr := '  ««"' ~ $nodesNodeStr;
    }
    my $extraStr := $node.dump_extra_node_info;
    my $prefix := $indent;
    if $isBlockChild {
        $prefix := $prefix ~ ($isLastChild ?? ($isLastChild == 2 ?? '─' !! '╙') !! '╟' );
    } else {
        $prefix := $prefix ~ ($isLastChild ?? ($isLastChild == 2 ?? '─' !! '└') !! '├' );
    }
    
    if nqp::istype($node, QAST::SpecialArg) {
        $clsStr := nqp::substr($clsStr, 0, nqp::index($clsStr, '+{'));
        $extraStr := $extraStr ~ ' :flat(' ~ $node.flat ~ ')' if $node.flat;
        $extraStr := $extraStr ~ ' :named("' ~ nqp::escape($node.named) ~ '")' if $node.named;
    }
    $extraStr := $extraStr ?? ' ' ~ $extraStr !! '';
    if $clsStr eq 'Op' {
        $extraStr := nqp::substr($extraStr, 1);
        $clsStr := $extraStr;
        $extraStr := '';
        $prefix := $prefix ~ '─';
    } elsif $clsStr eq 'Var' {
        $clsStr := '';
        #$extraStr := nqp::substr($extraStr, 1);
        $prefix := $prefix ~ '○';
    } elsif nqp::substr($clsStr, 1, 3) eq 'Val' {
        $prefix := $prefix ~ '■ ';
    } elsif $clsStr eq 'Block' {
        $prefix := $prefix ~ '─:';
    } elsif nqp::substr($clsStr, 0, 4) eq 'Stmt' {
        $prefix := $prefix ~ '─:';
    } else {
        $prefix := $prefix ~ '─';
    }
    my @lines := [$prefix ~ $clsStr ~ $extraStr ~ $nodesNodeStr];
    #my @lines := [$prefix ~ $node.HOW.name($node) ~ ($extraStr ?? '(' ~ $extraStr ~ ')' !! '') ~ $nodesNodeStr];
    my $i := nqp::elems($node.list);
    my $childIndent := $indent ~ ($isLastChild ?? '  ' !! ($isBlockChild ?? '║ ' !! '│ '));
    my $iamblock := nqp::istype($node, QAST::Block);
    for $node.list {
        @lines.push(dump($_, $childIndent, :isLastChild(--$i == 0), :isBlockChild($iamblock)));
    }
    nqp::join("\n", @lines);
}




sub istypeAny($subject, *@types) {
    for @types {
        return 1 if nqp::istype($subject, $_);
    }
    return 0;
}


sub qastChildren($ast, *@types) {
    nqp::die('qastChildren expects a QAST::Node as 1st arg - got ' ~ nqp::reprname($ast) )
        unless nqp::istype($ast, QAST::Node);
    my @out := [];
    if nqp::elems(@types) == 0 {
        @types := [QAST::Node];
    }
    for $ast.list {
        if istypeAny($_, |@types) {
            @out.push($_);
        }
    }
    @out;
}

sub drop_takeclosure($ast) {
    nqp::die('drop_takeclosure expects a QAST::Node - got ' ~ nqp::reprname($ast) )
        unless nqp::istype($ast, QAST::Node);
    if nqp::istype($ast, QAST::Op) && $ast.op eq 'takeclosure' {
        $ast := drop_takeclosure($ast[0]);  #   $ast[0];    #   
    #} elsif nqp::istype($ast, QAST::Children) {
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

sub _drop_Stmts($ast, $parent) {
    nqp::die('dropStmts expects a QAST::Node - got ' ~ nqp::reprname($ast) ~ (nqp::isstr($ast) ?? ' "' ~ nqp::escape($ast) ~ '"' !! '') )
        unless nqp::istype($ast, QAST::Node);

    if nqp::can($ast, 'resultchild') && nqp::isint($ast.resultchild) {
        return [$ast];   # don't muck with that...
    }

    my @children := [];
    for $ast.list {
        for _drop_Stmts($_, $ast) {
            @children.push($_);
        }
    }
    if nqp::istype($ast, QAST::Stmts)
        && (
              istypeAny($parent, QAST::CompUnit, QAST::Block, QAST::Stmts, QAST::Stmt) 
           || (nqp::elems(@children) < 2)
        )
    {
        return @children; # return the Stmts' children as is, dropping the Stmts node
    } else {
        #$ast.set_children(@children);
        my @list := $ast.list;
        while +@list { @list.pop }
        for @children { @list.push($_) }
    }

    return [$ast];
}

sub drop_Stmts($ast) {
    my @out := _drop_Stmts($ast, nqp::null);
    nqp::elems(@out) == 1
        ?? @out[0]
        !! QAST::Stmts.new(|@out);
}

sub isinResultPosition($node, $parent) {
    my $n := nqp::elems($parent) - 1;
    if ($parent[$n] =:= $node) || (nqp::can($parent, 'resultchild') && $parent[$parent.resultchild] =:= $node) {
        return 1;
    }
    
    while --$n >= 0 {
        return 0 if $node =:= $parent[$n];
    }

    nqp::die(whatsit($node) ~ ' not a child of ' ~ whatsit($parent));
}


sub drop_bogusVars($ast, $parent = nqp::null) {
    if nqp::istype($ast, QAST::Var) && !$ast.decl {
        if istypeAny($parent, QAST::Block, QAST::Stmt, QAST::Stmts) {
            unless isinResultPosition($ast, $parent) {
                #nqp::print(whatsit($parent) ~ ' ' ~ $ast.dump);
                return nqp::null;
            }
        }
    } elsif +$ast.list { # workaround - not all nodes with children actually do that role
        #say('  >> ', whatsit($ast), ' ', nqp::elems($ast.list));
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

sub repair_null_decl_attrs_of_vars($ast) {
    nqp::die('remove_bogusOpNames expects a QAST::Node - got ' ~ nqp::reprname($ast) )
        unless nqp::istype($ast, QAST::Node);
    if nqp::istype($ast, QAST::Var) && !$ast.decl {
        $ast.decl(nqp::null_s);
    } else {
        for $ast.list {
            repair_null_decl_attrs_of_vars($_);
        }
    }
    $ast;
}

sub remove_bogusOpNames($ast) {
    nqp::die('remove_bogusOpNames expects a QAST::Node - got ' ~ nqp::reprname($ast) )
        unless nqp::istype($ast, QAST::Node);
    if nqp::istype($ast, QAST::Op) && ($ast.op ne 'call') && ($ast.op ne 'callstatic') && ($ast.op ne 'callmethod') && ($ast.op ne 'lexotic') {
        #say('>>>Op(', $ast.op, ' ', $ast.dump_extra_node_info, ')')
        #    unless nqp::index('x radix can postinc preinc add_n sub_n stringify bind bindkey concat atpos atkey die reprname defor isnull iseq_s iseq_n isgt_n islt_n isinvokable isstr isint isnum islist ishash substr if unless for while elems chars escape list hash iterkey_s iterval', $ast.op) >= 0;
        $ast.name(nqp::null_s);
    }
    for $ast.list {
        remove_bogusOpNames($_);
    }
    $ast;
}

sub removeChild($parent, $child) {
    my @children := nqp::islist($parent) ?? $parent !! $parent.list;
    my @foundAt := [];
    my $i := 0;
    my $n := nqp::elems(@children);
    for @children {
        if $_ =:= $child {
            @foundAt.push($i);
        }
        $i++;
    }
    unless +@foundAt {
        nqp::die("could not find child " ~ whatsit($child) ~ ' under ' ~ $parent.dump);
    }

    my @removed := [];
    @foundAt.push($n);
    $i := @foundAt.shift;
    my $k := $i + 1;
    for @foundAt {
        while $k < $_ {
            @children[$i++] := @children[$k++];
        }
        @removed.push(@children[$k++]);
    }
    nqp::setelems(@children, $n - nqp::elems(@removed));
    $parent;
}


sub remove_MAIN($ast) {
    say($ast[0].cuid);
    say("CompUnit load: \n", dump($ast.load, '   '));
    say("CompUnit main: \n", dump($ast.main, '   '));

    my @path := [];
    my $MAIN := findDef($ast, '&MAIN', @path);
    removeChild(@path[0], $MAIN);
    say(whatsit(@path), "\n", dump($MAIN));
    @path := [];
    my $MAINcall := findPath(-> $node, @pathUp {
            if nqp::istype($node, QAST::Op) && ($node.op eq 'call') && ($node.name eq '&MAIN' || (nqp::istype($node[0], QAST::Var) && $node[0].name eq '&MAIN')) {
                my $parent := @pathUp[0];
                if nqp::istype($parent, QAST::Op) && $parent.op eq 'if' {
                    $parent;
                } elsif istypeAny($parent, QAST::Stmt, QAST::Stmts) {
                    $parent := @pathUp[0];
                    if nqp::istype($parent, QAST::Op) && $parent.op eq 'if' {
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
    #say(whatsit(@path), ' ', $MAINcall.dump);
    $ast;
}


sub findPath(&test, $node, @pathUp = []) {
    my $res := &test($node, @pathUp);
    if nqp::islist($res) {
        @pathUp.unshift($node);
        for $res {
            my $res2 := findPath(&test, $_, @pathUp);
            return $res2 if $res2;  # ie. if truthy (list, 1 or a node)
        }
        @pathUp.shift();
    } elsif $res {
        if $res =:= $node || !nqp::istype($res, QAST::Node) {    # just truthy to indicate that $node should be returned
            return $node
        } else {
            while !($res =:= @pathUp.shift) {
            }
            return $res;
        }
    }
    return nqp::null;
}


sub findDef($ast, str $name, @pathUp = []) {
    findPath(
        -> $node, @pathUp {
            my $parent := nqp::elems(@pathUp) > 0 ?? @pathUp[0] !! nqp::null;
            if nqp::isnull($parent) || nqp::istype($parent, QAST::CompUnit) {
                $node.list;
            } elsif nqp::istype($parent, QAST::Op) && nqp::istype($node, QAST::Var) {
                 $parent.op eq 'bind' && $node.name eq $name && $node.decl
                    ?? $parent
                    !! nqp::null;
            } elsif istypeAny($parent, QAST::Block, QAST::Stmts, QAST::Stmt, QAST::Op) {
                my @next := qastChildren($node, QAST::Block, QAST::Stmts, QAST::Stmt, QAST::Var, QAST::Op); # TODO: put Op nodes first
                @next;
            } else {
                0;
            }
        },
        $ast, @pathUp
    );
}


sub renameVars($ast, $map?) {
    nqp::die('renameVars expects a QAST::Node as 1st arg - got ' ~ nqp::reprname($ast) )
        unless nqp::istype($ast, QAST::Node);
    if nqp::defined($map) {
        nqp::die('renameVars expects a unary fn as 2nd arg(optional) - got ' ~ nqp::reprname($map) )
            unless nqp::isinvokable($map);
    } else {
        $map := -> str $name { $name };
    }
    if nqp::istype($ast, QAST::Var) 
       || (
          nqp::istype($ast, QAST::Op)
          && (($ast.op eq 'call') || ($ast.op eq 'callstatic'))
        ) {
        my str $old := $ast.name;
        my str $new := $map($old);
        if $new ne $old {
            $ast.name($new);
        }
    }
    #if nqp::istype($ast, QAST::Children) {
    if nqp::can($ast, 'list') { # workaround - not all nodes with children actually do that role
        for $ast.list {
            renameVars($_, $map);
        }
    }
    $ast;
}

# -----------------------------------------------



role StrByDump {
    method Str() { dump(self) }
}

class SmartCompiler is NQP::Compiler {

    method BUILD() {
        # in this order (!):
        self.addstage('ast_save',     :after<ast>);
        #self.addstage('optimize',    :before<ast_save>);

        # Add extra command line options.
        my @clo := self.commandline_options();
        @clo.push('parsetrace');
        @clo.push('setting=s');
        @clo.push('setting-path=s');
        @clo.push('module-path=s');
        @clo.push('no-regex-lib');
        @clo.push('stable-sc');
        @clo.push('optimize=s');
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
    
    method ast_clean($ast, *%adverbs) {
        say(">>>ast_clean ", self.user-progname(), '...');
        
        #$ast := drop_takeclosure($ast);  # breaks things!!!!!!
        
        $ast := drop_Stmts($ast);
        $ast := drop_bogusVars($ast);       # do this *after* drop_Stmts !!!
        $ast := repair_null_decl_attrs_of_vars($ast);
        $ast := remove_bogusOpNames($ast);
        $ast := remove_MAIN($ast);

        $ast := renameVars($ast, -> $s {
            my str $fst := nqp::substr($s, 0, 1);
            my str $snd := nqp::substr($s, 1, 1);
            $fst eq '&' || $snd eq 'λ'
                ??  '.' ~ nqp::substr($s, 1)
                !! $s;
        });

        my $what := '&lam2info';  #   '&strOut';  #   '&renameVars';  #   '&ifTag';    #   
        #$ast := findDef($ast, $what);
        say($what, ' not found!')
            unless $ast;

        $ast;
    }
    

    method ast_save($ast, *%adverbs) {
        my $qastfileName := self.user-progname() ~ '.qast';
        return $ast
            if %adverbs<output> eq $qastfileName;
        spew($qastfileName, ~$ast);
        say(">>>ast_save: QAST dump written to ", $qastfileName);
        $ast;
    }

}


my $needsCompilation := 0;

class NQPCompiler is SmartCompiler {

    method BUILD() {
        self.language('nqp');
        self.parsegrammar(NQP::Grammar);
        self.parseactions(NQP::Actions);

        return self;
    }


    method handle-exception($error) {
        nqp::rethrow($error);
    }

    method compileFile($file, :$lib = '.', :$target = 'mbc') {
        my $nqpName := "$lib/$file.nqp";
        #say("<nqpc> $nqpName: target=$target ");
        my $qastName := "$nqpName.qast";
        my $mvmName := "$lib/$file.moarvm";
        if !nqp::filereadable($nqpName) {
            nqp::die("no such file: $nqpName");
        }
        if nqp::stat($mvmName, nqp::const::STAT_EXISTS) && !nqp::filewritable($mvmName) {
            nqp::die("cannot write to file: $mvmName");
        }
        my $nqpTime := nqp::stat($nqpName, nqp::const::STAT_MODIFYTIME);
        my $mvmTime := nqp::filewritable($mvmName)
            ?? nqp::stat($mvmName, nqp::const::STAT_MODIFYTIME)
            !! 0
        ;
        $needsCompilation := 1; #$needsCompilation || ($nqpTime > $mvmTime);
        if !$needsCompilation {
            return nqp::null;   # means: "not compiled (again) because it was up-to-date"
        } else {
            my @opts := [
                #'--stagestats',
                '--module-path=' ~ $lib,
                '--target=' ~ $target,
            ];
            if $target eq 'mbc' {
                @opts.push('--output=' ~ $mvmName);
            } elsif $target eq 'ast' || $target eq 'clean_ast' || $target eq 'ast_save' {
                @opts.push('--output=' ~ $qastName);    # not only write it but also prevent NQP::Compiler to dump it to stdout and return a null
            }
            my @args := nqp::clone(@opts);
            @args.unshift('nqpc');  # give it a program name (for command_line)
            @args.push($nqpName);
            #say($mvmName, '...');

            say("<nqpc> ", nqp::join(' ', @args));
            #say(nqp::x('-', 29));
            my $*USER_FILE := $nqpName;
            my $result;
            my $error;
            try {
                $result := self.command_line(@args, :encoding('utf8'), :transcode('ascii iso-8859-1'));
                CATCH {
                    $error := $_;
                }
            }
            unless $error {
                if nqp::isnull($result) {   # returning non-null means: "yes, we did compile and write it to disk"
                    if $target eq 'mbc' {
                        $result := $mvmName;
                    } else {
                        nqp::die("??? - successfully compiled $nqpName to target $target - but got null result...!?");
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
                say('Error: missing module "', $file ~ '"');
            } elsif nqp::index($msglc, 'unable to write bytecode') > -1 {
                $from := nqp::index($msglc, '\'') + 1;
                $to   := nqp::index($msglc, '\'', $from);
                my $file := nqp::substr($msg, $from, $to - $from);
                my $line := 1;
                $msg := nqp::join('', [
                          'Error: ', $msg,
                    "\n", '  at ', $nqpName, ':', ~$line,
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
                    "\n", '  at ', $nqpName, ':', ~$line,
                    "\n"
                ]);
            } elsif nqp::index($msglc, 'assignment ("=") not supported ') > -1 {
                $from := nqp::index($msglc, 'at line') + 1;
                $from := nqp::findcclass(nqp::const::CCLASS_NUMERIC, $msglc, $from, nqp::chars($msglc) - $from);
                $to   := nqp::findnotcclass(nqp::const::CCLASS_NUMERIC, $msglc, $from, nqp::chars($msglc) - $from);
                my $line := nqp::substr($msg, $from, $to - $from);
                $line := max(1, $line - 1);
                my @lines := linesFrom($nqpName, $line, 2);
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
                    "\n", '   at ', $nqpName, ':', ~$line, ($column ?? ':' ~ $column !! ''),
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
                    "\n", '   at ', $nqpName, ':', ~$line, ($column ?? ':' ~ $column !! ''),
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
    my $cwd := nqp::cwd();
    my $lib := 'lib/L';    #   '.';     #   
    my $ext := '.nqp';
    my $sep := '# [nqpc] ' ~ nqp::x('-', 29);
    my $nqpc := NQPCompiler.new();
    my %opts := hash();

    @ARGS.shift;  # first is program name

    if nqp::elems(@ARGS) == 0 {
        #@ARGS.push('LGrammar');
        #@ARGS.push('LActions');
        #@ARGS.push('L');

        @ARGS.push('runtime');
        $nqpc.addstage('ast_clean', :before<ast_save>);
        %opts<target> := '';    # ...and run it
    }


    for @ARGS {
        my $file := $_ ~ $ext;
        my $result := $_ eq 'nqpc'
            ?? $nqpc.compileFile($_, :lib('.'),  |%opts)
            !! $nqpc.compileFile($_, :lib($lib), |%opts);
        say(nqp::isnull($result)
            ?? "# [nqpc] uptodate: $lib/$file"
            !! "# [nqpc] compiled: $lib/$file ~> " ~ whatsit($result)
        );
        CATCH {
            my $msg := nqp::join('', [
                  "# [nqpc] ", "   ERROR: $lib/$file",
                "\n", $sep,
                "\n# [nqpc] ", "     CWD: $cwd",
                "\n# [nqpc] ", "     lib: $lib",
                "\n# [nqpc] ", '    ARGS: ', nqp::join(' ', @ARGS),
                "\n# [nqpc] ",
                "\n# [nqpc] ", ~$_,
            ]);
            say($msg);
            nqp::exit(1);
            
            #nqp::die($msg);    # cannot do this: sometimes "Memory allocation failed; could not allocate zu bytes"
        }
    }
    say($sep);
}

