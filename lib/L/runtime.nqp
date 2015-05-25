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

sub lam2code($lambda) {
    nqp::atpos($lambda, 1);
}

sub lam2info($lambda) {
    my $id      := nqp::atpos($lambda, 0);
    my $idx     := nqp::atpos(nqp::radix(10, $id, 1, 0), 0);
    my %rawInfo := %info<λ>[$idx];
    my %out     := nqp::hash(
        'id',       $id,
        'idx',      $idx,
        'from',     %rawInfo<from>,
        'length',   %rawInfo<length>,
        'src',      nqp::substr($λsrc, %rawInfo<from>, %rawInfo<length>),
    );
    # --- up to here it was all the same for all instances ---

    my @fvs     := sublist($lambda, 2);    # freeVars start at 2
    my %fvs     := nqp::hash();
    my @fvns := %rawInfo<freeVarNames>;
    my $i := 0; # TODO: use nqp::iterator(@fvs)
    for @fvns {
        nqp::bindkey(%fvs, $_, @fvs[$i]);
        $i++;
    }
    nqp::bindkey(%out, 'freeVars', %fvs);
    %out;
}

sub fellthroughtypecase($subject) {
    nqp::die('typecase: fell through due to missing "otherwise"-callback: ' ~ nqp::reprname($subject));
}


sub typecase($subject, *%callbacks) {
    say('>>>typecase(', nqp::reprname($subject), '...)');
    my $otherwise := nqp::defor(
        %callbacks<otherwise>,
        &fellthroughtypecase
    );
    my $cbKey;
    if nqp::islist($subject) {
        my $id := nqp::atpos($subject, 0);
        my $tag := nqp::substr($id, 0, 1);
        if $tag eq 'λ' {
            $cbKey := 'λ';
        } else {
            if nqp::elems($subject) == 0 {
                nqp::die('typecase: unsupported low-level list type - empty');
            } else {
                nqp::die('typecase: unsupported low-level list type - invalid tag ' ~ nqp::reprname($tag));
            }
        }
    } else {
        if nqp::isstr($subject) {
            $cbKey := 'str';
        } elsif nqp::isint($subject) {
            $cbKey := 'int';
        } elsif nqp::isnum($subject) {
            $cbKey := 'num';
        } else {
            nqp::die('typecase: unsupported low-level type ' ~ nqp::reprname($subject));
        }
    }
    my $cb := nqp::defor(%callbacks{$cbKey}, $otherwise);
    $cb($subject);
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

sub lam2strOut($lambda, str $indent = '', %done = {}) {
    my %info := lam2info($lambda);
    my $src := %info<src>;
    my %fvs := %info<freeVars>;
    for %fvs {
        my $fvName  := nqp::iterkey_s($_);
        my $fv      := nqp::iterval($_);
        my $pre := "# where $fvName = ";
        $src := $src ~ typecase($fv,
            :λ(-> $x {
                my %info    := lam2info($fv);
                my $id      := %info<id>;
                my $doneKey := "$fvName = $id";
                if %done{$doneKey} {
                    '';
                } else {
                    %done{$doneKey} := 1;
                    "\n$indent$pre" ~ lam2strOut($fv, $indent ~ '#' ~ nqp::x(' ', nqp::chars($pre) - 1), %done);
                }
            }),
            :otherwise(-> $x {
                my $doneKey := $pre ~ nonLam2strOut($fv);
                if %done{$doneKey} {
                    '';
                } else {
                    %done{$doneKey} := 1;
                    "\n$indent$doneKey";
                }
            })
        );
    }
    $src;
}


sub strOut($v, str $indent = '', %done = {}) {
    $v := force($v);
    typecase($v,
        :λ(&lam2strOut),
        :otherwise(&nonLam2strOut)
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

