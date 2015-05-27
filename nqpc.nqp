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
    } elsif nqp::isint($v)            { $reprname ~ ' ' ~ $v
    } elsif nqp::isnum($v)            { $reprname ~ ' ' ~ $v
    #} elsif nqp::istype($v, Something) { ??? } # TODO: something smart for lists and hashes
    } elsif nqp::can($v.HOW, 'name')  { $v.HOW.name($v)
    } else {
        $reprname
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

role StrByDump {
    method Str() { self.dump }
}

class SmartCompiler is NQP::Compiler {

    has @!qastInspectors;

    method BUILD() {
        @!qastInspectors := [];

        # in this order (!):
        self.addstage('optimize',    :after<ast>);
        self.addstage('inspectqast', :after<ast>);

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

    method add_qastInspector($consumer) {
        @!qastInspectors.push($consumer);
    }

    method inspectqast($ast, *%adverbs) {
        my $fileName := $*USER_FILE;
        
        for @!qastInspectors {
            $ast := $_($fileName, $ast);
        }
        return $ast;
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
            } elsif $target eq 'ast' || $target eq 'inspectqast' {
                @opts.push('--output=' ~ $qastName);
            }
            my @args := nqp::clone(@opts);
            @args.unshift('nqpc');  # give it a program name (for command_line)
            @args.push($nqpName);
            #say($mvmName, '...');

            #say("<nqpc> $nqpName ", nqp::join(' ', @args));
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
    #if nqp::istype($ast, QAST::Children) {
    if nqp::can($ast, 'list') { # workaround - not all nodes with children actually do that role
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
    }
    [$ast];
}

sub drop_Stmts($ast) {
    my @out := _drop_Stmts($ast, nqp::null);
    nqp::elems(@out) == 1
        ?? @out[0]
        !! QAST::Stmts.new(|@out);
}

sub remove_bogusOpNames($ast) {
    nqp::die('remove_bogusOpNames expects a QAST::Node - got ' ~ nqp::reprname($ast) )
        unless nqp::istype($ast, QAST::Node);
    #if nqp::istype($ast, QAST::Children) {
    if nqp::can($ast, 'list') { # workaround - not all nodes with children actually do that role
        for $ast.list {
            remove_bogusOpNames($_);
        }
    }
    if nqp::istype($ast, QAST::Op) && ($ast.op ne 'call') && ($ast.op ne 'callmethod') && ($ast.op ne 'lexotic') {
        #say('>>>Op(', $ast.op, ' ', $ast.dump_extra_node_info, ')')
        #    unless nqp::index('x radix can postinc preinc add_n sub_n stringify bind bindkey concat atpos atkey die reprname defor isnull iseq_s iseq_n isgt_n islt_n isinvokable isstr isint isnum islist ishash substr if unless for while elems chars escape list hash iterkey_s iterval', $ast.op) >= 0;
        $ast.name(nqp::null_s);
    }
    $ast;
}

sub findDef($ast, str $name) {
    my $out;
    if nqp::istype($ast, QAST::CompUnit) {
        return findDef(qastChildren($ast, QAST::Block)[0], $name);
    } elsif istypeAny($ast, QAST::Block, QAST::Stmts, QAST::Stmt) {
        for qastChildren($ast, QAST::Stmts, QAST::Stmt, QAST::Op) {
            if nqp::istype($_, QAST::Op) {
                if $_.op eq 'bind' && $_[0].name eq $name {
                    return $_;
                }
            } else {
                $out := findDef($_, $name);
                if $out {
                    return $out;
                }
            }
        }
    }
    $out;
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
    if nqp::istype($ast, QAST::Var) || (nqp::istype($ast, QAST::Op) && ($ast.op eq 'call')) {
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


sub MAIN(*@ARGS) {
    my $cwd := nqp::cwd();
    my $lib := 'lib/L';    #   '.';     #   
    my $ext := '.nqp';
    my $sep := '# [nqpc] ' ~ nqp::x('-', 29);
    my $nqpc := NQPCompiler.new();

    @ARGS.shift;  # first is program name

    if nqp::elems(@ARGS) == 0 {
        #@ARGS.push('LGrammar');
        #@ARGS.push('LActions');
        #@ARGS.push('L');

        @ARGS.push('runtime');
    }

    my $inspector := -> $fileName, $ast {
        my $what := '&lam2info';  #   '&strOut';  #   '&renameVars';  #   '&ifTag';    #   
        say(">>> $fileName...");
        #$ast := drop_takeclosure($ast);  # breaks things!!!!!!
        $ast := drop_Stmts($ast);
        $ast := remove_bogusOpNames($ast);
        #$ast := findDef($ast, $what);
        if $ast {
            $ast := renameVars($ast, -> $s {
                my str $fst := nqp::substr($s, 0, 1);
                my str $snd := nqp::substr($s, 1, 1);
                if $fst eq '&' || $snd eq 'λ' {
                    '.' ~ nqp::substr($s, 1);
                } else {
                    $s;
                }
            });
            my $dump := $ast.dump;
            my $qastfileName := $fileName ~ '.qast';
            spew($qastfileName, $dump);
            say(">>> QAST dump written to ", $qastfileName);
        } else {
            say($what, ' not found!');
        }
        $ast;
    };

    $nqpc.add_qastInspector($inspector)
        if +@ARGS == 1 && @ARGS[0] eq 'runtime';

    for @ARGS {
        my $file := $_ ~ $ext;
        my $result := $_ eq 'nqpc'
            ?? $nqpc.compileFile($_, :lib('.'))
            !! $nqpc.compileFile($_, :lib($lib));
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

