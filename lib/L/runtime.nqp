my $λsrc := '(λf.λstart.λxs.xs start (λhd.λtl.self f (f start hd) tl)) (λ_.x)';
my %info := nqp::hash(
    'λ', [
        nqp::hash('from',  1, 'length', 55, 'freeVarNames', ['foo', 'bar', 'baz', 'qumbl', 'self', 'self']),
        nqp::hash('from', 59, 'length',  4, 'freeVarNames', ['foo']),
    ],
);

sub force($v) {
    nqp::isinvokable($v) ?? $v() !! $v;
}

sub strLit(str $s) {
    '"' ~ nqp::escape($s) ~ '"';
}

sub sublist(@list, int $from) {
    my int $n     := nqp::elems(@list);
    my int $count := $n;
    my int $to    := $from + $count;
    my     @out   := [];
    if $to > $n {
        $to := $n
    }
    while $from < $to {
        @out.push(@list[$from]);
        $from++;
    }
    @out;
}

sub lam2info($lambda, str $id, int $idx, %rawLambdaInfo) {
    my @fvs     := sublist($lambda, 2);    # freeVars start at 2
    my %fvs     := nqp::hash();
    my %out     := nqp::hash(
        'id',       $id,
        'idx',      $idx,
        'from',     %rawLambdaInfo<from>,
        'length',   %rawLambdaInfo<length>,
        'src',      nqp::substr($λsrc, %rawLambdaInfo<from>, %rawLambdaInfo<length>),
        'code',     nqp::atpos($lambda, 1),
        'freeVars', %fvs
    );
    my @fvns := %rawLambdaInfo<freeVarNames>;
    my $i := 0; # TODO: use nqp::iterator(@fvs)
    for @fvns {
        nqp::bindkey(%fvs, $_, @fvs[$i]);
        $i++;
    }
    %out;
}

sub ifTag($subject, str $tag, $then, $else) {
    say(">>>ifTag(..., $tag, ...)");
    if nqp::islist($subject) {
        my $id := nqp::atpos($subject, 0);
        if nqp::substr($id, 0, 1) eq $tag {
            my $idx := nqp::atpos(nqp::radix(10, $id, 1, 0), 0);
            my $rawInfo := %info{$tag}[$idx];
            $then(lam2info($subject, $id, $idx, $rawInfo));
        } else {
            force($else);
        }
    } else {
        force($else);
    }
}

sub nonLam2strOut($v) {
    if nqp::isstr($v) {
        strLit($v);
    } elsif nqp::isint($v) {
        ~$v;
    } elsif nqp::isnum($v) {
        ~$v;
    } else {
        nqp::reprname($v);
    }
}

sub lam2strOut(%info, str $indent = '', %done = {}) {
    my $src := %info<src>;
    my %fvs := %info<freeVars>;
    for %fvs {
        my $fvName  := nqp::iterkey_s($_);
        my $fv      := nqp::iterval($_);
        my $pre := "# where $fvName = ";
        ifTag($fv, 'λ', 
            -> %info {
                my $id      := %info<id>;
                my $doneKey := "$fvName = $id";
                unless %done{$doneKey} {
                    %done{$doneKey} := 1;
                    $src := $src 
                        ~ "\n$indent$pre"
                        ~ lam2strOut(%info, $indent ~ '#' ~ nqp::x(' ', nqp::chars($pre) - 1), %done)
                    ;
                }
            },
            {
                my $doneKey := $pre ~ nonLam2strOut($fv);
                unless %done{$doneKey} {
                    %done{$doneKey} := 1;
                    $src := $src ~ "\n$indent$doneKey";
                }
            }
        );
    }
    $src;
}


sub strOut($v, str $indent = '', %done = {}) {
    $v := force($v);
    ifTag($v, 'λ',
        -> %info {
            lam2strOut(%info, $indent, %done);
        },
        { nonLam2strOut($v) }
    );
}


sub MAIN(*@ARGS) {
    my $lambda2 := [
        'λ1',                           # id: tag 'λ' and idx into %λinfo
        -> *@as { 'λ1(...) called' },   # code
        23,                             # freeVars (ie values of)
    ];
    my $lambda1 := [
        'λ0',                               #  id: tag 'λ' and idx into %λinfo
        -> *@as { 'λ0(...) called' },       # code
        'foo', 42, 3.14159265, $lambda2     # freeVars (ie values of)
    ];
    $lambda1.push($lambda1);    # add a self (recursive) ref
    $lambda1.push($lambda1);    # add a self (recursive) ref
    
    say(strOut($lambda1));
}

