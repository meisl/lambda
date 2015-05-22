use nqp;
use NQPHLL;


sub max($a, $b) { $a > $b ?? $a !! $b }
sub min($a, $b) { $a < $b ?? $a !! $b }

class NQPCompiler is NQP::Compiler {
    
    method handle-exception($error) {
        nqp::rethrow($error);
    }
    
    method inspectQAST($ast) {
        #say(">>>nqpc.inspectQAST: ", $ast.dump);
        return $ast;
    }
    
}


sub setupCompiler() {
    # Create and configure compiler object.
    my $nqpcomp := NQPCompiler.new();
    $nqpcomp.language('nqp');
    $nqpcomp.parsegrammar(NQP::Grammar);
    $nqpcomp.parseactions(NQP::Actions);

    $nqpcomp.addstage('optimize', :after<ast>);
    $nqpcomp.addstage('inspectQAST', :before<optimize>);

    # Add extra command line options.
    my @clo := $nqpcomp.commandline_options();
    @clo.push('parsetrace');
    @clo.push('setting=s');
    @clo.push('setting-path=s');
    @clo.push('module-path=s');
    @clo.push('no-regex-lib');
    @clo.push('stable-sc');
    @clo.push('optimize=s');
    
    return $nqpcomp;
}

my $nqpCompiler := setupCompiler();

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

my $needsCompilation := 0;

sub compile($file, :$lib, :$cwd) {
    my $nqpName := "$lib/$file.nqp";
    my $mvmName := "$lib/$file.moarvm";
    if !nqp::filereadable($nqpName) {
        nqp::die("no such file: $nqpName");
    }
    if !nqp::filewritable($mvmName) {
        nqp::die("cannot write to file: $mvmName");
    }
    my $nqpTime := nqp::stat($nqpName, nqp::const::STAT_MODIFYTIME);
    my $mvmTime := nqp::filewritable($mvmName)
        ?? nqp::stat($mvmName, nqp::const::STAT_MODIFYTIME)
        !! 0
    ;
    $needsCompilation := 1;     # $needsCompilation || ($nqpTime > $mvmTime);
    if !$needsCompilation {
        #say($mvmName, ' ');
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
        my $result;
        my $error;
        try {
            $result := $nqpCompiler.command_line(@args, :encoding('utf8'), :transcode('ascii iso-8859-1'));
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
    }
    return 0;
}

sub MAIN(*@ARGS) {
    my %hash := hash();
    my $cwd := nqp::cwd();
    my $lib := 'lib/L';
    
    
    @ARGS.shift;  # first is program name

    if nqp::elems(@ARGS) == 0 {
        @ARGS.push('LGrammar');
        @ARGS.push('LActions');
        @ARGS.push('L');
    }

    for @ARGS {
        compile($_, :lib($lib), :cwd($cwd));
        CATCH {
            my $msg := nqp::join('', [
                      'CWD: ', $cwd,
                "\n", 'lib: ', $lib,
                "\n", 'ARGS: ', nqp::join(' ', @ARGS),
                "\n", nqp::x('-', 29),
                "\n", ~$_,
            ]);
            say($msg);
            nqp::exit(1);
            
            #nqp::die($msg);    # cannot do this: sometimes "Memory allocation failed; could not allocate zu bytes"
        }
    }
}

