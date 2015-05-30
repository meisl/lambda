my $λsrc := '(λf.λstart.λxs.xs start (λhd.λtl.self f (f start hd) tl)) (λ_.x)';
my %info := nqp::hash(
    'λ', [
        'binder0 1 55 foo bar baz qumbl self self',
        'binder1 59 4 foo',
    ],
);

# inlineables? ----------------------------------------------------------------

sub LAMFIELD_ID()       is export { 0 }
sub LAMFIELD_CODE()     is export { 1 }
sub LAMFIELD_FREEVARS() is export { 2 }

sub lam2id($lam)   { $lam[LAMFIELD_ID()] }
sub lam2code($lam) { $lam[LAMFIELD_CODE()] }
sub lam2fvs($lam)  { sublist($lam, LAMFIELD_FREEVARS()) }

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
    my $infoIt  := nqp::iterator(nqp::split(' ', %info<λ>[$idx]));
    my $binder  := nqp::shift($infoIt);  # nqpc would convert a methodcall .shift
    my $from    := nqp::shift($infoIt);  # nqpc would convert a methodcall .shift
    my $length  := nqp::shift($infoIt);  # nqpc would convert a methodcall .shift
    my %out     := nqp::hash(
        'id',       $id,
        'idx',      $idx,
        'binder',   $binder,
        'from',     $from,
        'length',   $length,
        'src',      nqp::substr($λsrc, $from, $length),
    );
    # --- up to here it was all the same for all instances ---

    my $varsIt  := nqp::iterator(lam2fvs($lambda));
    my $namesIt := $infoIt;
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
    my $cbKey := nqp::null;
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

