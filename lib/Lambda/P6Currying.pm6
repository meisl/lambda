use v6;


my $nApp_c = 0; # "complete" application
my $nApp_o = 0; # "over-" application
my $nApp_p = 0; # "partial" application
my $nCurry = 0; # calls to sub curry (without early exits)
my $nCurry_ttl = 0; # calls to sub curry

my constant %fnStats = Hash.new;

my role CurryStats {
    method gist { self.Str }
    method Str {
        my $result = "CurryStats: {self<partial>}p, {self<complete>}f, {self<over>}o, {self<curry>}+{self<curry_ttl>-self<curry>}i";
        
        $result ~= "\n";
        my @entries = %fnStats.values\
            .grep({ $_<full>.defined && $_<fn>.?symbol eq any('Term->source', '#true', '#false', <_if K>) })   #    <LamT AppT VarT [LamT] [AppT] [VarT] id I Y B K const cons nil _if _and _or #true #false>) })
        ;
        my %classified = @entries\
            .classify({$_<full>});
        
        my &fn2Str = -> $fn { ($fn.?symbol // $fn.?lambda // typeof($fn)) };
        #my &fn2Str = -> $fn { ($fn.gist };
        
        my $s = %classified\
            .sort({ $^a.key < $^b.key})\
            #.map(-> (:$key, :value(@vs)) { "$key ({+@vs}): " ~ @vs.map(-> (:$fn, *%_) { &fn2Str($fn) }).join(', ') })\
            .map(-> (:$key, :value(@vs)) { "$key ({+@vs}): " ~ @vs.map(-> (:$fn, *%_) { &fn2Str($fn) ~ "({%_.perl})" }).join(', ') })\
            #.map(-> $x { $x.WHAT })\
            .join("\n")
        ;
        #$result ~= %fnStats.grep(-> (:$key, :$value) { $value<fn>.?symbol eq 'Term->source'}).perl;
        #$result ~= @entries.map(-> (:$fn, *%_) { $fn.symbol ~ '|' ~ $fn.WHERE => %_ }).perl;
        $result ~= $s;

        $result;
    }
}

sub curryStats is export {
    { partial => $nApp_p,
      complete => $nApp_c,
      over => $nApp_o,
      curry => $nCurry,
      curry_ttl => $nCurry_ttl,
    } does CurryStats;
}

sub stats-key-individual(&f) {
    #&f.gist;                # not working because type changes (roles may be added later) & dangerous because .gist might *apply* the fn again ~> inf regression
    #&f.do.WHICH.Str;        # not working if objects are moved by GC
    #&f.WHICH.Str;           # not working because type changes (ObjAt, roles may be added later)
    #&f.WHICH.WHERE.Str;     # not working if objects are moved by GC (real mem-address of ObjAt)
    &f.WHICH.Str.substr(&f.WHAT.perl.Str.chars + 1);    # this is only the (pseudo) "mem-address" of the ObjAt, guaranteed to stay the same
}

sub stats-key(&f) {
    #stats-key-individual(&f);
    &f.?symbol // stats-key-individual(&f);     # if we do recursion with the generic Y, then every rec. calls yields a new fn...
}

sub stats-entry(&f) {
    my $key = stats-key(&f);
    my $out = %fnStats{$key};
    return $out
        if $out.defined;
    $out = %fnStats{$key} //= (fn => &f, key => $key, init => 0, init-bogus => 0, part => 0, full => 0, over => 0).hash;
    #if $key ~~ /\d+/ {
    #    $out<bt> = Backtrace.new;
    #}
    return $out;
}

sub stats-inc(&f, *@fieldNames) {
    my $entry = stats-entry(&f);
    for @fieldNames -> $fieldName {
        my $v = $entry{$fieldName}++;
    }
    return $entry;
}


my sub captureToStr(Capture:D $capture) {
    "\\({$capture.list.map(*.perl).join(', ')}"
        ~ ($capture.hash > 0 
            ?? ', ' ~ $capture.hash.pairs.map(-> $p { $p.key ~ ' => ' ~ $p.value.perl }).join(', ')
            !! '')
        ~ ')'
}

class X::Typing is X::TypeCheck is export {
    has Str $.operation = 'curried fn application';
}

class X::Typing::UnsupportedNamedArgs is X::Typing is export {
    has Str $.message;
    has     $.whatsInFuncPos;
    has     $!args;
    method  args        { captureToStr($!args)    }

    has Str $.expected  = 'positional args only';
    method  got         { self.args }

    multi method new(Callable:D :$whatsInFuncPos!, Capture:D :$args!) {
        self.bless(:$whatsInFuncPos, :$args);
    }

    multi method new(Callable:D $whatsInFuncPos, Capture:D $args) {
        self.bless(:$whatsInFuncPos, :$args);
    }

    submethod BUILD(:$!whatsInFuncPos, :$!args) {
        $!message = "named args not supported for curried fn {$!whatsInFuncPos.WHICH}; got {self.args}";
    }
}

class X::Typing::ArgBinding is X::Typing is export {
    has Str $.message;
    has     $.whatsInFuncPos;
    has     $!args;
    method  args        { captureToStr($!args)    }

    method  expected    { typeof($!whatsInFuncPos) }
    method  got         { self.args }

    multi method new(Callable:D :$whatsInFuncPos!, Capture:D :$args!) {
        self.bless(:$whatsInFuncPos, :$args);
    }

    multi method new(Callable:D $whatsInFuncPos, Capture:D $args) {
        self.bless(:$whatsInFuncPos, :$args);
    }

    submethod BUILD(:$!whatsInFuncPos, :$!args) {
        $!message = "cannot apply {$!whatsInFuncPos.gist}: {self.expected} to {self.got}";
    }
}

class X::Typing::Unapplicable is X::Typing is export {
    has Str $.message;
    has     $.whatsInFuncPos;
    has     $!args;
    method  args        { captureToStr($!args)    }

    has Str $.expected  = 'a function to apply';
    method  got         { ~$!whatsInFuncPos.WHICH }
    
    submethod BUILD(:$!whatsInFuncPos, :$!args) {
        $!message = "cannot apply non-function {self.got} to {self.args}";
    }
}

my sub dieUnapplicable($self, Capture:D $args) {
    die X::Typing::Unapplicable.new(:whatsInFuncPos($self), :$args);
}

my role Unapplicable {
    multi method invoke(Capture:D $args) {  # TODO: remove once Rakudo* 2015-02 has landed
        dieUnapplicable(self, $args);
    }
    multi method invoke(|args) {    # "over-applying" will come here
        dieUnapplicable(self, args);
    }
}


# gets called if none of the signatures matches (~> invalid call)
my sub dieArgBinding($self, Capture:D $args) is hidden_from_backtrace {
    die X::Typing::ArgBinding.new($self, $args)
}

my sub dieNamedArgs($self, Capture:D $args) is hidden_from_backtrace {
    die X::Typing::UnsupportedNamedArgs.new($self, $args)
}

my sub dieInvalidArgs($self, Capture:D $args) is hidden_from_backtrace {
    ?$args.hash and dieNamedArgs($self, $args) or dieArgBinding($self, $args)
}


my sub types(&f, $n = 0) is export {
    my $s = &f.signature;
    @($s.params[$n..*].map(*.type), $s.returns)
}

my sub typeof(&f, $n = 0) is export {
    types(&f, $n).map(*.perl).join(' -> ');
}

role Curried {...}
role P       {...}


my proto sub apply_comp(|) {*}

my multi sub apply_comp($self, Callable     $result)            { curry($result)            }  # 460
my multi sub apply_comp($self, Curried      $result) is default { $result                   }  #   0
my multi sub apply_comp($self, Unapplicable $result)            { $result                   }  # 223
my multi sub apply_comp($self,              $result)            { $result does Unapplicable }  #  65

&apply_comp.wrap(-> $self, |rest {
    $nApp_c++;
    stats-inc($self, 'full');
    nextsame; 
});

my proto sub apply_more(|) {*}

my multi sub apply_more($self, Callable     $f, @rest)            {              curry($f).invoke(|@rest) }
my multi sub apply_more($self, Curried      $f, @rest) is default {                     $f.invoke(|@rest) }
my multi sub apply_more($self, Unapplicable $f, @rest)            {                     $f.invoke(|@rest) }
my multi sub apply_more($self,              $f, @rest)            { ($f does Unapplicable).invoke(|@rest) }

&apply_more.wrap(-> $self, |rest {
    $nApp_o++;
    stats-inc($self, 'over');
    nextsame;
});


my sub apply_part(&self, Mu $do, *@args) {
    my @types = types(&self, +@args);
    given @types {
        when 2 { return { $do(|@args, $^b)                 } does P[|@types] }
        when 3 { return { $do(|@args, $^b, $^c)            } does P[|@types] }
        when 4 { return { $do(|@args, $^b, $^c, $^d)       } does P[|@types] }
        when 5 { return { $do(|@args, $^b, $^c, $^d, $^e)  } does P[|@types] }
    }
}

&apply_part.wrap(-> $self, |rest {
    $nApp_p++;
    stats-inc($self, 'part');
    nextsame;
});


my role P[::T1, ::TR] does Curried[T1, TR] {
    has Signature $!s;
    method signature { $!s //= EVAL ":(T1 -->TR)" }
}

my role P[::T1, ::T2, ::TR] does Curried[T1, T2, TR] {
    has Signature $!s;
    method signature { $!s //= EVAL ":(T1, T2 -->TR)" }
}

my role P[::T1, ::T2, ::T3, ::TR] does Curried[T1, T2, T3, TR] {
    has Signature $!s;
    method signature { $!s //= EVAL ":(T1, T2, T3 -->TR)" }
}

my role P[::T1, ::T2, ::T3, ::T4, ::TR] does Curried[T1, T2, T3, T4, TR] {
    has Signature $!s;
    method signature { $!s //= EVAL ":(T1, T2, T3, T4 -->TR)" }
}

my role P[::T1, ::T2, ::T3, ::T4, ::T5, ::TR] does Curried[T1, T2, T3, T4, T5, TR] {
    has Signature $!s;
    method signature { $!s //= EVAL ":(T1, T2, T3, T4, T5 -->TR)" }
}

# arity 1
role Curried[::T1, ::TR] {
    has &!do = nqp::getattr(nqp::decont(self), Code, '$!do');

    multi method invoke(T1 $a1                               , *%()) { apply_comp(self, &!do( $a1)    ) }
    multi method invoke(T1 $a1, *@_($, *@)                   , *%()) { apply_more(self, &!do( $a1), @_) }

    multi method invoke(|as) { dieInvalidArgs(self, as) }

    multi method invoke(Capture:D $as) { self.invoke(|$as) }  # TODO: remove once Rakudo* 2015-02 has landed
}


# arity 2
role Curried[::T1, ::T2, ::TR] {
    has &!do = nqp::getattr(nqp::decont(self), Code, '$!do');

    multi method invoke(T1 $a1                               , *%()) { apply_part(self, &!do, $a1          ) }
    multi method invoke(T1 $a1, T2 $a2                       , *%()) { apply_comp(self, &!do( $a1, $a2)    ) }
    multi method invoke(T1 $a1, T2 $a2, *@_($, *@)           , *%()) { apply_more(self, &!do( $a1, $a2), @_) }

    multi method invoke(|as) { dieInvalidArgs(self, as) }

    multi method invoke(Capture:D $as) { self.invoke(|$as) }  # TODO: remove once Rakudo* 2015-02 has landed
}


# arity 3
role Curried[::T1, ::T2, ::T3, ::TR] {
    has &!do = nqp::getattr(nqp::decont(self), Code, '$!do');

    multi method invoke(T1 $a1                               , *%()) { apply_part(self, &!do, $a1               ) }
    multi method invoke(T1 $a1, T2 $a2                       , *%()) { apply_part(self, &!do, $a1, $a2          ) }
    multi method invoke(T1 $a1, T2 $a2, T3 $a3               , *%()) { apply_comp(self, &!do( $a1, $a2, $a3)    ) }
    multi method invoke(T1 $a1, T2 $a2, T3 $a3, *@_($, *@)   , *%()) { apply_more(self, &!do( $a1, $a2, $a3), @_) }

    multi method invoke(|as) { dieInvalidArgs(self, as) }

    multi method invoke(Capture:D $as) { self.invoke(|$as) }  # TODO: remove once Rakudo* 2015-02 has landed
}


# arity 4
role Curried[::T1, ::T2, ::T3, ::T4, ::TR] {
    has &!do = nqp::getattr(nqp::decont(self), Code, '$!do');

    multi method invoke(T1 $a1                                    , *%()) { apply_part(self, &!do, $a1                    ) }
    multi method invoke(T1 $a1, T2 $a2                            , *%()) { apply_part(self, &!do, $a1, $a2               ) }
    multi method invoke(T1 $a1, T2 $a2, T3 $a3                    , *%()) { apply_part(self, &!do, $a1, $a2, $a3          ) }
    multi method invoke(T1 $a1, T2 $a2, T3 $a3, T4 $a4            , *%()) { apply_comp(self, &!do( $a1, $a2, $a3, $a4)    ) }
    multi method invoke(T1 $a1, T2 $a2, T3 $a3, T4 $a4, *@_($, *@), *%()) { apply_more(self, &!do( $a1, $a2, $a3, $a4), @_) }

    multi method invoke(|as) { dieInvalidArgs(self, as) }

    multi method invoke(Capture:D $as) { self.invoke(|$as) }  # TODO: remove once Rakudo* 2015-02 has landed
}


# arity 5
role Curried[::T1, ::T2, ::T3, ::T4, ::T5, ::TR] {
    has &!do = nqp::getattr(nqp::decont(self), Code, '$!do');

    multi method invoke(T1 $a1                                            , *%()) { apply_part(self, &!do, $a1                         ) }
    multi method invoke(T1 $a1, T2 $a2                                    , *%()) { apply_part(self, &!do, $a1, $a2                    ) }
    multi method invoke(T1 $a1, T2 $a2, T3 $a3                            , *%()) { apply_part(self, &!do, $a1, $a2, $a3               ) }
    multi method invoke(T1 $a1, T2 $a2, T3 $a3, T4 $a4                    , *%()) { apply_part(self, &!do, $a1, $a2, $a3, $a4          ) }
    multi method invoke(T1 $a1, T2 $a2, T3 $a3, T4 $a4, T5 $a5            , *%()) { apply_comp(self, &!do( $a1, $a2, $a3, $a4, $a5)    ) }
    multi method invoke(T1 $a1, T2 $a2, T3 $a3, T4 $a4, T5 $a5, *@_($, *@), *%()) { apply_more(self, &!do( $a1, $a2, $a3, $a4, $a5), @_) }

    multi method invoke(|as) { dieInvalidArgs(self, as) }

    multi method invoke(Capture:D $as) { self.invoke(|$as) }  # TODO: remove once Rakudo* 2015-02 has landed
}



sub curry(&f -->Callable) is export {
    $nCurry_ttl++;

    if &f ~~ Curried {
        stats-inc(&f, 'init-bogus');
        return &f;
    }

    $nCurry++;
    my $sig = &f.signature;

    my @ps = $sig.params;

    die "cannot curry fn with optional/slurpy/named/capture or parcel parameters - signature: {$sig.perl}; fn: {&f.gist}"
        if @ps.map({$_.optional || $_.slurpy || $_.named || $_.capture || $_.parcel}).any;
    
    try {
        my $g = &f does Curried[|@(@ps.map(*.type), $sig.returns)];
        #stats-init($g); # create entry and set field "init" to 1
        stats-inc($g, 'init');
        return $g;
    }

    my $arity = $sig.arity;

    die "cannot curry nullary fn - signature: {$sig.perl}; fn: {&f.gist}" 
        if $arity == 0;

    die "NYI: Fn with arity $arity (> 5) - signature: {$sig.perl}; fn: {&f.gist}"
        if $arity > 5;
}
