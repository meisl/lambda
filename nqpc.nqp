use nqp;
use NQPHLL;


sub max($a, $b) { $a > $b ?? $a !! $b }
sub min($a, $b) { $a < $b ?? $a !! $b }

sub linesFrom(str $filename, $from = 1, $count?) {
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


class NQPCompiler is NQP::Compiler {

    has @!qastInspectors;

    method BUILD() {
        @!qastInspectors := [];
        #say(">>>>BUILD: self=", nqp::reprname(self));
        self.language('nqp');
        self.parsegrammar(NQP::Grammar);
        self.parseactions(NQP::Actions);

        self.addstage('optimize', :after<ast>);
        self.addstage('inspectQAST', :before<optimize>);

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
    

    method add_qastInspector($consumer) {
        @!qastInspectors.push($consumer);
    }

    method inspectQAST($ast) {
        my $fileName := $*USER_FILE;
        for @!qastInspectors {
            $_($fileName, $ast);
        }
        return $ast;
    }

    method handle-exception($error) {
        nqp::rethrow($error);
    }
}


my $needsCompilation := 0;

sub compile($nqpc, $file, :$lib, :$cwd) {
    my $nqpName := "$lib/$file.nqp";
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
    $needsCompilation := $needsCompilation || ($nqpTime > $mvmTime);
    if !$needsCompilation {
        #say($mvmName, ' ');
        return 0;   # means: "not compiled (again) because it was up-to-date"
    } else {
        my @opts := [
            '--module-path=' ~ $lib,
            '--target=mbc',
            '--output=' ~ $mvmName,
        ];
        my @args := nqp::clone(@opts);
        @args.unshift('nqpc');  # give it a program name (for command_line)
        @args.push($nqpName);
        #say($mvmName, '...');

        #say(nqp::join(' ', @args));
        #say(nqp::x('-', 29));
        my $*USER_FILE := $nqpName;
        my $result;
        my $error;
        try {
            $result := $nqpc.command_line(@args, :encoding('utf8'), :transcode('ascii iso-8859-1'));
            CATCH {
                $error := $_;
            }
        }
        if $error {
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
            } else {
                my $line := 1;
                my $column;
                $msg := nqp::join('', [
                          'ERROR: ', $msg,
                    "\n", '   at ', $nqpName, ':', ~$line, ($column ?? ':' ~ $column !! ''),
                    "\n",
               ]);
            }
            nqp::flushfh(nqp::getstdout());
            nqp::die($msg);
        }
        return 1;   # means: "yes, we did compile and write it to disk"
    }
}

sub MAIN(*@ARGS) {
    my $cwd := nqp::cwd();
    my $lib := 'lib/L';
    my $ext := '.nqp';
    my $sep := '# [nqpc] ' ~ nqp::x('-', 29);
    my $nqpc := NQPCompiler.new();

    #$nqpc.add_qastInspector(-> $fileName, $ast {
    #    say(">>> $fileName\n", $ast.dump);
    #});

    @ARGS.shift;  # first is program name

    if nqp::elems(@ARGS) == 0 {
        #@ARGS.push('LGrammar');
        #@ARGS.push('LActions');
        #@ARGS.push('L');
        @ARGS.push('foo');
    }

    for @ARGS {
        my $file := $_ ~ $ext;
        my $result := compile($nqpc, $_, :lib($lib), :cwd($cwd));
        say($result
            ?? "# [nqpc] compiled: $lib/$file"
            !! "# [nqpc] uptodate: $lib/$file",
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

