
my $needsCompilation := 0;

sub compile($file, :$lib, :$cwd) {
    my $nqpName := "$lib/$file.nqp";
    my $mvmName := "$lib/$file.moarvm";
    if !nqp::filewritable($nqpName) {
        nqp::die("no such file: $nqpName");
    }
    my $nqpTime := nqp::stat($nqpName, nqp::const::STAT_MODIFYTIME);
    my $mvmTime := nqp::filewritable($mvmName)
        ?? nqp::stat($mvmName, nqp::const::STAT_MODIFYTIME)
        !! 0
    ;
    $needsCompilation := $needsCompilation || ($nqpTime > $mvmTime);
    if !$needsCompilation {
        say($mvmName, ' ');
    } else {
        my $cmd := 'nqp-m.bat '
            ~ '--module-path="' ~ $lib ~ '" '
            ~ '--target=mbc '
            ~ '--output="' ~ $mvmName ~ '" '
            ~ $nqpName;
        #say($cmd);
        say($mvmName, '...');
        return nqp::shell($cmd, $cwd, hash());
    }
    return 0;
}

sub MAIN(*@ARGS) {
    my $cwd := nqp::cwd();
    my $lib := 'lib/L';
    #say('CWD: ', $cwd);
    @ARGS.shift;  # first is program name
     for @ARGS {
        my $error := compile($_, :lib($lib), :cwd($cwd));
        if $error {
            #nqp::die("Compile Error: ", $error);
            nqp::exit($error);
        }
    }

    say('--------------------------------');
}
