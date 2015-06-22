#!nqp

use Util;


class TreeWalkDo {
    has $!take;
    has $!howtocontinue;

    my @instances;
    my @CONTINUE;   # names how to continue (ie a mapping of index to string)
    my %CONTINUE;   # mapping of names how to continue to indices
    my @EXPLAIN;    # descriptions of what the specific how-to-continue means

    method take() { $!take }
    method Str()  { 
        ($!take ?? 'take-and-' !! 'skip-and-') ~ @CONTINUE[$!howtocontinue];
    }
    method nqp()  { 
        'TreeWalkDo.' ~ @CONTINUE[$!howtocontinue] ~ '(:' ~ ($!take ?? '' !! '!') ~ 'take)';
    }

    method explain() {
        if nqp::isconcrete(self) {
            ($!take ?? 'take' !! 'skip') ~ ' current node, then ' ~ @EXPLAIN[$!howtocontinue];
        } else {
            my @lines := [
                'TreeWalkDo: returned from callback in a tree walk in order to indicate',
                '  a) What to do with the current node:',
                '     - :take or :take(1) has the current node passed to the consumer.',
                '       Note: *when* this happens depends on the kind of walk (DFS vs BFS, bottom-up vs top-down).',
                '     - :!take or :take(0) (aka "skip"): current node is not passed to consumer.',
                '  b) How to continue:'
            ];
            for @CONTINUE {
                @lines.push("     - $_: " ~ @EXPLAIN[%CONTINUE{$_}]);
            }
            nqp::join("\n", @lines);
        }
    }

    INIT {
        my $i := nqp::iterator([
            'recurse',  'visit children, recursively',
            'return',   'stop here and continue with siblings of current node (ie don\'t visit its children)',
            'last',     'stop visiting siblings of current node and continue with parent\'s',
            'break',    'stop the entire walk but do pass nodes taken so far to consumer (including current node, if taken)',
            'halt',     'stop the entire walk, don\'t call consumer anymore (except for current node, if taken)',
        ]);
        @CONTINUE := [];
        @EXPLAIN  := [];
        while $i {
            @CONTINUE.push(nqp::shift($i));
            @EXPLAIN.push(nqp::shift($i));
            
        }
        %CONTINUE := {};
        @instances := [[], []];
        for 0, 1 -> $take {
            my $howtocontinue := 0;
            my @is := @instances[$take];
            for @CONTINUE {
                @is.push(TreeWalkDo.new(:$take, :$howtocontinue));
                %CONTINUE{$_} := $howtocontinue++;
            }
        }
    }

    my sub do($which, $take, $howtocontinue) {
        my $i := %CONTINUE{$which};
        nqp::isconcrete($howtocontinue) && $take =:= NO_VALUE
            ?? $howtocontinue == $i
            !! @instances[$take ?? 1 !! 0][$i];
    }

    method recurse(:$take = NO_VALUE) { do('recurse', $take, self ?? $!howtocontinue !! self) }
    method return (:$take = NO_VALUE) { do('return',  $take, self ?? $!howtocontinue !! self) }
    method last   (:$take = NO_VALUE) { do('last',    $take, self ?? $!howtocontinue !! self) }
    method break  (:$take = NO_VALUE) { do('break',   $take, self ?? $!howtocontinue !! self) }
    method halt   (:$take = NO_VALUE) { do('halt',    $take, self ?? $!howtocontinue !! self) }
}



class TreeWalk {

    my sub _children($n) { nqp::islist($n) ?? $n !! (nqp::can($n, 'list') ?? $n.list !! []) }
    
    my sub _dfs-up(&probe, &consumer, $node, $index, @pathUp, &children) {
        my $x := &probe($node, @pathUp);
        my $y := TreeWalkDo.return;
        my $redo := 0;
        if $x.recurse {
            my $i := 0;
            @pathUp.unshift($node);
            while $i < nqp::elems(&children($node)) {
                my @result := _dfs-up(&probe, &consumer, &children($node)[$i], $i, @pathUp, &children);
                $y := @result[0];
                my $redoChild := @result[1];
                unless $redoChild {
                    $i++;
                    last if $y.last || $y.break || $y.halt;
                }
            }
            @pathUp.shift;
        }
        if $x.take && !$y.halt {
            my $z := &consumer($node, @pathUp);
            if istype($z, TreeWalk) {
                nqp::splice(&children(@pathUp[0]), $z.payload, $index, 1);
                $redo := 1;
            }
        }
        if $y.break || $y.halt {
            $y, $redo;
        } else {
            $x, $redo;
        }
    }
    
    method dfs-up(&probe, &consumer, $node, :&children = &_children) {
        _dfs-up(&probe, &consumer, $node, -1, [], &children);
        $node;
    }

    has $!payload;

    method payload() {
        $!payload;
    }

    method replace(*@xs) {
        TreeWalk.new(:payload(@xs));
    }

    method remove() {
        TreeWalk.new(:payload([]));
    }


}



sub MAIN(*@ARGS) {
    say(TreeWalkDo.explain);

    sub check($do) {
        nqp::say($do ~ '.nqp     = ' ~ $do.nqp);
        nqp::say($do ~ '.explain = ' ~ $do.explain);

        nqp::say($do ~ '.take    = ' ~ $do.take);
        nqp::say($do ~ '.recurse = ' ~ $do.recurse);
        nqp::say($do ~ '.return  = ' ~ $do.return);
        nqp::say($do ~ '.last    = ' ~ $do.last);
        nqp::say($do ~ '.break   = ' ~ $do.break);
        nqp::say($do ~ '.halt    = ' ~ $do.halt);
        nqp::say('');
        
    }

    my $do1 := TreeWalkDo.recurse(:take);
    



    check($do1);
    check($do1.recurse(:take(!$do1.take)));
    check($do1.return(:take(!$do1.take)));
    check($do1.last(:!take));
    check($do1.break(:take));
    check($do1.halt(:take));
}
