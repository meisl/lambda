use v6;
use Lambda::P6Currying_common;

module Lambda::P6Currying_Stats;


# `wrapCurry` below will set this to the type of roles Curried/Partial from P6Currying
my $CurriedType;
my $PartialType;
my $isStatsEnabled = False;

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

my class PerFnStatsEntry is StatsEntry {
    my $maxKeyLen = 0;
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
            $fn ?? ' ' ~ &!fn.^roles.grep({$_ ~~ none(Callable, $CurriedType, $PartialType)}).map(*.perl).grep({$_ eq none <lambda Definition>}).join('+') ~
                    ':(' ~ typeof(&!fn) ~ ')'
                !! ''
        );
    }
}


my constant %fnStats = Hash.new;
my constant $globalStats = StatsEntry.new;



my sub fn2Str($fn) { $fn.name || typeof($fn) };
#my sub fn2Str($fn) { $fn.gist };


my sub entries(Code $filter?) {
    my @out = %fnStats.values;
    $filter.defined
        ?? @out.grep($filter)
        !! @out;
}

my sub byKeyLen(Code $filter?) {
    entries($filter).sort( { $^a.key.chars < $^b.key.chars} );
}

our sub curryStats is export {
    my $result = 'CurryStats: ';
    
    return $result ~ 'n/a'
        unless $isStatsEnabled;
    
    $result ~= $globalStats;
    
    $result ~= "\n";
    my @entries = entries({ 
        False
        || ($_.full >= 50)
        || ($_.fn ~~ $PartialType)
        || ($_.fn.name // '') eq any('Term->source', 'Term-eq?', 'Str-eq?', '#true', '#false', <LamT AppT VarT [LamT] [AppT] [VarT] id I const K K^2 Y B cons nil _if _and _or not>)
        || ($_.fn.name // '').substr(0, 5) eq 'subst'
    });
    my %classified = @entries\
        .classify(*.full);
    
    my $s = %classified\
        .sort({ $^a.key < $^b.key})\
        #.map(-> (:$key, :value(@vs)) { "$key ({+@vs}): " ~ @vs.map(-> (:$fn, *%_) { &fn2Str($fn) }).join(', ') })\
        .map(-> (:$key, :value(@vs)) { sprintf("%5d (%3d): %s", $key, +@vs, @vs.map(-> $entry { sprintf("%13s => %s", &fn2Str($entry.fn), $entry.Str(:no-key)) }).join(', ')) })\
        #.map(-> $x { $x.WHAT })\
        .join("\n")
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

my sub statsWrapper_full($self, |rest) {
    $globalStats.full++;
    stats($self).full++;
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


my sub wrapCurry(&curry, $curriedType, $partialType) is export {
    &curry.wrap(&statsWrapper_curry);
    $CurriedType = $curriedType;
    $PartialType = $partialType;
    $isStatsEnabled = True;
}

my sub wrapApp(:&part!, :&full!, :&over!) is export {
    &part.wrap(&statsWrapper_part);
    &full.wrap(&statsWrapper_full);
    &over.wrap(&statsWrapper_over);
}

