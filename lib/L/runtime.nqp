my $λsrc := '(λf.λstart.λxs.xs start (λhd.λtl.self f (f start hd) tl)) (λ_.x)';
my %info := nqp::hash(
    'λ', [
        nqp::hash('from',  1, 'length', 55, 'freeVarNames', ['foo', 'bar', 'baz', 'qumbl', 'self', 'self']),
        nqp::hash('from', 59, 'length',  4, 'freeVarNames', ['foo']),
    ],
);


# inlineables? ----------------------------------------------------------------

sub lam2id($lam)   { $lam[0] }
sub lam2code($lam) { $lam[1] }
sub lam2fvs($lam)  { sublist($lam, 2) }

sub int2str(int $i) { ~$i }
sub num2str(num $n) { ~$n }
# did you expect `str2str`? - that's `strLit`
sub strLit(str $s) { '"' ~ nqp::escape($s) ~ '"' }

# -----------------------------------------------------------------------------


sub force($v) {
    nqp::isinvokable($v) ?? $v() !! $v;
}

sub delayMemo($block) {
    my int $wasRun := 0;
    my $result := nqp::null;
    my $out := {
        if $wasRun {
            $result;
        } else {
            $wasRun := 1;
            $result := $block();
        }
    };
    $out;
}

sub sublist(@list, int $from) is export {
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


sub lam2info($lambda) {
    my $id      := lam2id($lambda);
    my $idx     := nqp::radix(10, $id, 1, 0)[0];
    my %rawInfo := %info<λ>[$idx];
    my %out     := nqp::hash(
        'id',       $id,
        'idx',      $idx,
        'from',     %rawInfo<from>,
        'length',   %rawInfo<length>,
        'src',      nqp::substr($λsrc, %rawInfo<from>, %rawInfo<length>),
    );
    # --- up to here it was all the same for all instances ---

    my $varsIt  := nqp::iterator(lam2fvs($lambda));
    my $namesIt := nqp::iterator(%rawInfo<freeVarNames>);
    my %fvs     := {};
    while $varsIt {
        %fvs{nqp::shift($namesIt)} := nqp::shift($varsIt);  # nqpc would convert a methodcall .shift
    }
    %out<freeVars> := %fvs;
    %out;
}


sub typecase($subject, *%callbacks) {
    #say('>>>typecase(', nqp::reprname($subject), '...) ');
    my $otherwise := nqp::defor(
        %callbacks<otherwise>,
        -> $x { # compiler should see that this needs not be a closure
            nqp::die('typecase: fell through due to missing "otherwise"-callback: '
                ~ nqp::reprname($subject)
            )
        }
    );
    my $cbKey;# := nqp::null;
    if nqp::islist($subject) {
        my $id := $subject[0];
        my $tag := nqp::substr($id, 0, 1);
        if $tag eq 'λ' {
            $cbKey := $tag;
        } else {
            if nqp::elems($subject) == 0 {
                nqp::die('typecase: unsupported low-level list type - empty');
            } else {
                nqp::die('typecase: unsupported low-level list type - invalid tag ' ~ nqp::reprname($tag));
            }
        }
    } else {
             if nqp::isstr($subject) { $cbKey := 'str';
        } elsif nqp::isint($subject) { $cbKey := 'int';
        } elsif nqp::isnum($subject) { $cbKey := 'num';
        } else {
            nqp::die('typecase: unsupported low-level type ' ~ nqp::reprname($subject));
        }
    }
    my $cb := nqp::defor(%callbacks{$cbKey}, $otherwise);
    $cb($subject);
}


sub strOut($v, str $indent = '', %done = {}) {
    typecase(force($v),
        :λ(-> $lambda { # compiler should see that this needs not be a closure
            my %info := lam2info($lambda);
            my $src := %info<src>;
            for %info<freeVars> {
                my $fvName  := $_.key;
                my $fv      := $_.value;
                my $pre     := "# where $fvName = ";
                my $flatVal := typecase($fv,
                    :λ(-> $x { nqp::null }), # compiler should see that this needs not be a closure
                    :str(&strLit),
                    :int(&int2str),
                    :num(&num2str)
                );
                my $doneKey := nqp::isnull($flatVal)
                    ?? $pre ~ lam2id($fv)
                    !! $pre ~ $flatVal;
                unless %done{$doneKey} {
                    %done{$doneKey} := 1;
                    $src := $src ~ "\n" ~ $indent ~ (nqp::isnull($flatVal)
                        ?? $pre ~ strOut($fv, $indent ~ '#' ~ nqp::x(' ', nqp::chars($pre) - 1), %done)
                        !! $doneKey
                    );
                }
            }
            $src
        }),
        :str(&strLit),
        :int(&int2str),
        :num(&num2str)
    );
}

sub apply1($f, $a1) {
    my $result := typecase(force($f),
        :λ(&lam2code),
        :otherwise(-> $x {
            nqp::die('ERROR: cannot apply ' ~ strOut($x) ~ ' to ' ~ strOut($a1))
        })
    )($a1);
    force($result);
}

sub say(*@args) {
    my $it := nqp::iterator(@args);
    my $s  := '';
    my $_;
    while $it {
        $_ := nqp::shift($it);  # nqpc would convert a methodcall .shift
        $s := $s ~ (nqp::isstr($_)
            ?? $_
            !! strOut($_));
    }
    nqp::say($s);
}


sub MAIN(*@ARGS) {
    my $n := 0;
    my $b := { $n := $n + 1; };
    my $d := delayMemo($b);
    nqp::die('not ok: .delayMemo') unless $n == 0;
    nqp::die('not ok: .delayMemo') unless force($d) == 1;
    nqp::die('not ok: .delayMemo') unless force($d) == 1;
    nqp::die('not ok: .delayMemo') unless force($b) == 2;
    nqp::die('not ok: .delayMemo') unless force($b) == 3;
    nqp::die('not ok: .delayMemo') unless force($d) == 1;
    
    
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

