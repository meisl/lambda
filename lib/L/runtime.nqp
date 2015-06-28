my $λsrc := '(λf.λstart.λxs.xs start (λhd.λtl.self f (f start hd) tl)) (λ_.x)';
my %info := nqp::hash(
    'λ', [
        'binder0 1 55 foo bar baz qumbl self self',
        'binder1 59 4 foo',
    ],
    'stats', nqp::hash( # to be filled in by compiler
        STATS_QASTSIZE()    , -1, # size of tree
        STATS_BLOCKCOUNT()  , -1, # nr of Blocks
        STATS_LISTCOUNT()   , -1, # nr of Op(list)s
        STATS_LAMBDACOUNT() , -1, # nr of λs parsed
        STATS_IVALCOUNT()   , -1, # nr of IVals
        STATS_SVALCOUNT()   , -1, # nr of SVals
        STATS_SVALSIZE()    , -1, # ttl size of SVals
    ),
);


# inlineables? ----------------------------------------------------------------

sub LAMFIELD_ID()       { 0 }
sub LAMFIELD_CODE()     { 1 }
sub LAMFIELD_FREEVARS() { 2 }

sub lam2id($lam)    { $lam[LAMFIELD_ID()] }
sub lam2code($lam)  { $lam[LAMFIELD_CODE()] }
sub lam2fvs($lam)   { sublist($lam, LAMFIELD_FREEVARS()) }


sub STATS_QASTSIZE()     { 'Node'      }   # these must match the keys of SmartCompiler's collect_stats!
sub STATS_BLOCKCOUNT()   { 'Block'     }
sub STATS_LISTCOUNT()    { 'list'      }
sub STATS_LAMBDACOUNT()  { 'lambda'    }
sub STATS_CALLISHCOUNT() { 'callish'   }
sub STATS_IVALCOUNT()    { 'IVal'      }
sub STATS_SVALCOUNT()    { 'SVal'      }
sub STATS_SVALSIZE()     { 'SValChars' }


sub int2str(int $i) { ~$i }
sub num2str(num $n) { ~$n }
# did you expect `str2str`? - that's `strLit`
sub strLit(str $s) { '"' ~ nqp::escape($s) ~ '"' }


# -----------------------------------------------------------------------------


sub force($v) is export {
    nqp::isinvokable($v) ?? $v() !! $v;
}

sub delayMemo($block) is export {
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

sub join($sep, @pieces) {
    my $_;
    my $i := nqp::iterator(@pieces);
    my $s := '';
    if $i {
        $s := nqp::shift($i);  # nqpc would convert a methodcall .shift
        $s := strOut($s)
            unless nqp::isstr($s);
        while $i {
            $_ := nqp::shift($i);  # nqpc would convert a methodcall .shift
            $s := $s ~ $sep ~ (nqp::isstr($_)
                ?? $_
                !! strOut($_));
        }
    }
    $s;
}


sub say(*@args) {
    nqp::say(join('', @args));
}

sub stats() {
    my %stats := %info<stats>;
    join('', [
        %stats{STATS_LAMBDACOUNT() }, " lambdas\n",
        %stats{STATS_QASTSIZE()    }, " QAST::Node s\n",
        %stats{STATS_BLOCKCOUNT()  }, " QAST::Block s\n",
        %stats{STATS_LISTCOUNT()   }, " QAST::Op(list) s\n",
        %stats{STATS_IVALCOUNT()   }, " QAST::IVal s\n",
        %stats{STATS_SVALSIZE()    }, " chars ttl in ",
        %stats{STATS_SVALCOUNT()   }, " QAST::SVal s\n",
        "------------------------------------------------",
    ]);
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
    say(stats());
}

