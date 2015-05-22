
my %λinfo := [
    nqp::hash('from', 0, 'length', 3),
    nqp::hash(from => 4, length => 2),
];

sub force($v) {
    nqp::isinvokable($v) ?? $v() !! $v;
}

sub strOut($v, str $indent) {
    $v := force($v);
}

sub MAIN(*@ARGS) {
    say(strOut("bar", ''));
}
