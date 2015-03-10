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

my sub stats-key-individual(&f) {
    #&f.gist;                # not working because type changes (roles may be added later) & dangerous because .gist might *apply* the fn again ~> inf regression
    #&f.do.WHICH.Str;        # not working if objects are moved by GC
    #&f.WHICH.Str;           # not working because type changes (ObjAt, roles may be added later)
    #&f.WHICH.WHERE.Str;     # not working if objects are moved by GC (real mem-address of ObjAt)
    my $addr = &f.WHICH.Str.substr(&f.WHAT.perl.Str.chars + 1);    # this is only the (pseudo) "mem-address" of the ObjAt, guaranteed to stay the same

    #$addr = sprintf("%08X", $addr.Int);
    $addr;
}

our sub stats-key(&f) is export {
    #stats-key-individual(&f);

    # If we do recursion with the generic Y, then every rec. calls yields a new fn.
    # So at least this is a case where we want to subsume several different fn objects
    # under one stats entry.
    # Therefore we'll use the .name, if there is one.
    # Note: for *anonymous recursive functions* there will still be a new entry for each recursive call.
    &f.name || stats-key-individual(&f);
}
