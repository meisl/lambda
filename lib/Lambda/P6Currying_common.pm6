use v6;

module Lambda::P6Currying_common;


our sub types(&f, $n = 0) is export {
    my $s = &f.signature;
    @($s.params[$n..*].map(*.type), $s.returns)
}

our sub typeof(&f, $n = 0) is export {
    types(&f, $n).map(*.perl).join(' -> ');
}

our sub captureToStr(Capture:D $capture) is export {
    "\\({$capture.list.map(*.perl).join(', ')}"
        ~ ($capture.hash > 0 
            ?? ', ' ~ $capture.hash.pairs.map(-> $p { $p.key ~ ' => ' ~ $p.value.perl }).join(', ')
            !! '')
        ~ ')'
}
