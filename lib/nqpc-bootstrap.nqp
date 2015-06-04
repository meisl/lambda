#!nqp

sub fileexists(str $f) { nqp::stat($f, nqp::const::STAT_EXISTS) }
sub filemtime(str $f)  { nqp::stat($f, nqp::const::STAT_MODIFYTIME) }
sub fixslashes($f) {
    nqp::index(nqp::cwd(), '\\') > -1
        ?? nqp::join('\\', nqp::split('/', $f))
        !! nqp::join('/', nqp::split('\\', $f))
}
sub m2path($m) { fixslashes(nqp::join('/', nqp::split('::', $m))) }

sub m2src(str $m) { fixslashes('lib/' ~ m2path($m) ~ '.nqp') }
sub m2bin(str $m) { fixslashes('blib/' ~ m2path($m) ~'.moarvm') }

sub needsCompilation($m) {
    my $bin := m2bin($m);
    my $src := m2src($m);
    #say("$src: ", fileexists($bin) ?? filemtime($bin) - filemtime($src) !! -1);
    !fileexists($bin) || (filemtime($bin) < filemtime($src));
}

sub who($predicate, @xs) {
    my @out := [];
    for @xs {
        @out.push($_) if $predicate($_);
    }
    @out;
}

sub any($predicate, @xs) {
    nqp::elems(who($predicate, @xs)) > 0;
}

sub exec(*@pieces, :$whatwedo = NO_VALUE) {
    my $cwd := nqp::cwd();
    my $cmd := nqp::join(' ', @pieces);
    #say("> $cmd");
    my $out := nqp::shell($cmd, $cwd, nqp::getenvhash());
    if $out {
        $whatwedo := 'compiling ' ~ @pieces.pop
           if $whatwedo =:= NO_VALUE;
        nqp::sayfh(nqp::getstderr,
               nqp::x('-', 40)
             ~ "\nnqpc-bootstrap: ERROR $whatwedo -> return code $out"
             ~ "\nnqpc-bootstrap: CWD=$cwd"
             ~ "\nnqpc-bootstrap: cmd=$cmd"
        );
        nqp::exit($out);
    }
}

sub compileAll(@ms) {
    return 0 unless @ms;
    my $main    := @ms.pop; # last one assumed to be nqpc itself, will be run on itself
    my $mainsrc := '"' ~ m2src($main) ~ '"';   
    my $rakudo  := nqp::backendconfig()<prefix>;
    my $moarexe := fixslashes($rakudo ~ '/bin/moar.exe');
    my $nqplibs := fixslashes($rakudo ~ '/languages/nqp/lib');
    my $libpath := fixslashes('--libpath="' ~ $nqplibs ~ '"');
    my $moar    := fixslashes("$moarexe $libpath");
    my $nqp     := fixslashes($moar ~ ' "' ~ $nqplibs ~ '/nqp.moarvm"');
    my $cwd     := nqp::cwd();
    my @ss := [];
    for @ms {
        my $src  := '"' ~ m2src($_) ~ '"';
        @ss.push($src);
        exec($nqp, '--target=mbc', '--output="' ~ m2bin($_) ~ '"', $src);
    }
    @ms.push($main);
    @ss.push($mainsrc);
    exec($nqp, $mainsrc, $mainsrc, :whatwedo("running $mainsrc (interpreted) on itself"));
    my $ss := nqp::join(', ', @ss);
    my @problems := who(&needsCompilation, @ms);
    if @problems {
        nqp::sayfh(nqp::getstderr,
               nqp::x('-', 40)
             ~ "\nnqpc-bootstrap: ERROR bootstrapping from $ss"
             ~ "\nnqpc-bootstrap: still not up-to-date: " ~ nqp::join(', ', @problems)
        );
        nqp::exit(1);
    }
    say("nqpc-bootstrap: recompiled $ss");
}

my @ms := <testing L::LGrammar nqpc>;

compileAll(@ms) if any(&needsCompilation, @ms);

