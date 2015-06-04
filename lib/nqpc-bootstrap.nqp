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
    !fileexists($bin) || (filemtime($bin) < filemtime($src));
}

sub any($predicate, @xs) {
    for @xs { return 1 if $predicate($_) }
    0;
}

sub compileAll(@ms) {
    my $rakudo  := nqp::backendconfig()<prefix>;
    my $moarexe := fixslashes($rakudo ~ '/bin/moar.exe');
    my $nqplibs := fixslashes($rakudo ~ '/languages/nqp/lib');
    my $libpath := fixslashes('--libpath="' ~ $nqplibs ~ '"');
    my $moar    := fixslashes("$moarexe $libpath");
    my $nqp     := fixslashes($moar ~ ' "' ~ $nqplibs ~ '/nqp.moarvm"');
    my $cwd     := nqp::cwd();
    my @ss := [];
    for @ms {
        my $opts := '--target=mbc --output="' ~ m2bin($_) ~ '"';
        my $src  := '"' ~ m2src($_) ~ '"';
        @ss.push($src);
        my $cmd := "$nqp $opts $src";
        #say("> $cmd");
        my $out := nqp::shell($cmd, $cwd, nqp::getenvhash());
        nqp::die("nqpc-bootstrap: ERROR compiling $src"
             ~ "\nnqpc-bootstrap: CWD=$cwd"
             ~ "\nnqpc-bootstrap: cmd=$cmd"
            ) if $out;
    }
    say('nqpc-bootstrap: recompiled ' ~ nqp::join(', ', @ss));
}

my @ms := <testing L::LGrammar nqpc>;
compileAll(@ms)
    if any(&needsCompilation, @ms);

