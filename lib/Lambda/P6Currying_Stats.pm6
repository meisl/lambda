use v6;
use Lambda::P6Currying_common;

module Lambda::P6Currying_Stats;


# `init` will set this to the type of roles Curried/Partial from P6Currying
my $CurriedType;
my $PartialType;
my (&currySub, &partSub, &fullSub, &overSub);
my &unwrapAll;
my $isStatsEnabled = False;

our sub init($curriedType, $partialType, :&curry!, :&part!, :&full!, :&over!) {
    $CurriedType = $curriedType;
    $PartialType = $partialType;
    &currySub = &curry;
    &partSub  = &part;
    &fullSub  = &full;
    &overSub  = &over;
}


my class StatsEntry {
    has Int:D $.init-bogus is rw = 0;
    has Int:D $.init       is rw = 0;
    has Int:D $.part       is rw = 0;
    has Int:D $.full       is rw = 0;
    has Int:D $.over       is rw = 0;

    method gist { self.Str }
    method Str {
        sprintf('(%2dp, %6df, %2do, %4d+%di)',
            $!part, $!full, $!over, $!init, $!init-bogus
        );
    }
}

my sub rolesStripped(&fn) {
    &fn.^roles.grep({$_ ~~ none(Callable, $CurriedType, $PartialType)}).grep({$_.perl eq none <lambda Definition>})
}

my sub fn2Str($fn) { $fn.name || '<<' ~ (rolesStripped($fn).map(*.perl).join('+') || '???') ~ '>>' };


my $maxKeyLen = 0;
my class PerFnStatsEntry is StatsEntry {
    has       &.fn;
    has Str:D $.key;

    submethod BUILD(:&!fn) {
        $!key = stats-key(&!fn);
        $maxKeyLen max= $!key.chars;
    }

    method Str(Bool :$no-key = False, Bool :$fn = True) {
        sprintf('(%2dp, %6df, %2do, %4d+%2di%s%s)',
            self.part, self.full, self.over, self.init, self.init-bogus, 
            $no-key ?? '' !! ' ' ~ $!key,
            $fn ?? ' ' ~ rolesStripped(&!fn).map(*.perl).join('+') ~
                    ':(' ~ typeof(&!fn) ~ ')'
                !! ''
        );
    }
}


my constant %fnStats = Hash.new;
my constant $globalStats = StatsEntry.new;


my sub entries(Code $filter?) {
    my @out = %fnStats.values;
    $filter.defined
        ?? @out.grep($filter)
        !! @out;
}

my sub byKeyLen(Code $filter?) {
    entries($filter).sort( { $^a.key.chars < $^b.key.chars} );
}

my sub entryStats(PerFnStatsEntry:D $entry) {
    sprintf("%{$maxKeyLen}s => %s", &fn2Str($entry.fn), $entry.Str(:no-key))
}

my sub fnStats(&f) {
    entryStats(stats(&f));
}

my sub btFrame2Str ($frame) {
    my $code = $frame.code;
    if $code.^roles.map(*.perl).any eq 'lambda' {
        "  in lambda {fn2Str($code)} at {$frame.file}:{$frame.line}\n";
    } else {
        $frame.Str;
    };
}

our sub curryStats is export {
    my $result = 'CurryStats: ';
    
#    return $result ~ 'n/a'
#        unless $isStatsEnabled;
    
    $result ~= $globalStats;
    
    $result ~= "\n";
    my @entries = entries({ 
        False
        || ($_.full >= 50)
        || ($_.part + $_.over + $_.init-bogus >=  1)
        || ($_.fn ~~ $PartialType)
        || ($_.fn.name // '') eq any('Term->source', 'Term-eq?', 'Str-eq?', '#true', '#false', <Pair LamT AppT VarT [LamT] [AppT] [VarT] id I M const K K^2 Y B cons nil car cdr foldl foldr first exists _if _and _or not>)
        || ($_.fn.name // '').substr(0, 5) eq 'subst'
        || ($_.fn.name // '').substr(0, 6) eq 'findFP'
    });
    my %classified = @entries\
        .classify(*.full);
    
    my $s = %classified\
        .sort({ $^a.key < $^b.key})\
        #.map(-> (:$key, :value(@vs)) { "$key ({+@vs}): " ~ @vs.map(-> (:$fn, *%_) { &fn2Str($fn) }).join(', ') })\
        .map(-> (:$key, :value(@vs)) {
            sprintf("%5d (%3d): %s", 
                $key, 
                +@vs, 
                @vs.map(
                    &entryStats
                ).sort.join(",\n" ~ (' ' x 13))
            )
        }).join("\n")
    ;
    $result ~= $s;

    $result;
}


sub stats(&f?) is export {
    return $globalStats
        unless &f.defined;
    my $key = stats-key(&f);
    my $out = %fnStats{$key};
    return $out
        if $out.defined;
    $out = %fnStats{$key} //= PerFnStatsEntry.new(fn => &f);
    #if $key ~~ /\d+/ {
    #    $out<bt> = Backtrace.new;
    #}
    return $out;
}


my sub statsWrapper_part($self, |rest) {
    $globalStats.part++;
    stats($self).part++;
    my $out = callsame;
    stats($out);    # make sure we have a PerFnStatsEntry for the partially applied fn
    return $out;
};

sub skip(List:D $list, &predicate) {
    $list[$list.first-index(&predicate)..*];
}

my sub statsWrapper_full($self, |rest) {
    $globalStats.full++;
    stats($self).full++;

#    if ($self.name // '') eq 'VarT->name' {
#        my $bt = Backtrace.new\
#        #.grep({
#        .first({
#            !(   $_.is-setting 
#              || $_.file ~~ /(P6Currying.+|\.nqp)$/
#            )
#        }).map(&btFrame2Str).join('');
#        note "full app: {fnStats($self)}\n" ~ $bt;
#    }

    nextsame; 
};

my sub statsWrapper_over($self, |rest) {
    $globalStats.over++;
    stats($self).over++;
    nextsame;
};

my sub statsWrapper_curry(&f, |rest) {
    if &f ~~ $CurriedType {
        $globalStats.init-bogus++;
        stats(&f).init-bogus++;
        nextsame;
    } else {
        my &out = callsame;
        $globalStats.init++;
        stats(&out).init++;
        return &out;
    }
}


our sub is_enabled() {
    $isStatsEnabled;
}

our sub set_enabled(Bool $enabled) {
    if $isStatsEnabled !== $enabled {
        $isStatsEnabled = $enabled;
        if $enabled {
            #say "stats off -> on";
            my $curryHandle = &currySub.wrap(&statsWrapper_curry);
            my $partHandle  = &partSub.wrap(&statsWrapper_part);
            my $fullHandle  = &fullSub.wrap(&statsWrapper_full);
            my $overHandle  = &overSub.wrap(&statsWrapper_over);
            &unwrapAll = -> {
                 &currySub.unwrap($curryHandle);
                 &partSub.unwrap($partHandle);
                 &fullSub.unwrap($fullHandle);
                 &overSub.unwrap($overHandle);
            };
        } else {
            #say "stats on -> off";
            &unwrapAll();
        }
    }
}
