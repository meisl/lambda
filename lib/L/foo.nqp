my $λsrc := 'λf.λstart.λxs.xs start (λhd.λtl.self f (f start hd) tl)';
my %λinfo := [
    nqp::hash('from', 0, 'length', 55, 'freeVarNames', ['self']),
];

sub force($v) {
    nqp::isinvokable($v) ?? $v() !! $v;
}

sub strOut($v, str $indent, $depth = 0) {
    $v := force($v);
    if nqp::isstr($v) {
        '"' ~ nqp::escape($v) ~ '"';
    } else {
        my @fvs := $v<freeVars>;
        my $idx := $v<infoIdx>;
        my %info := %λinfo[$idx];
        my @fvns := %info<freeVarNames>;
        my $src := nqp::substr($λsrc, %info<from>, %info<length>);
        my $i := 0;

        for @fvs -> $fv {
            my $fvName := @fvns[$i];
            my $pre := "# where $fvName = ";
            $src := $src ~
                "\n$indent$pre"
            ;
            if $depth > 2 {
                $src := $src ~ '...';
            } else {
                $src := $src ~ strOut($fv, $indent ~ nqp::x(' ', nqp::chars($pre)), $depth + 1);
            }
            $i++;
        }
        $src;
    }
}

sub MAIN(*@ARGS) {
    my $lambda := nqp::hash(
        'infoIdx', 0,
        'freeVars', [],
    );
    $lambda<freeVars>.push($lambda);
    say(strOut($lambda, ''));
}
