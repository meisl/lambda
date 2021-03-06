use v6;

use Lambda::P6Currying_common;
use Lambda::P6Currying_X;
use Lambda::P6Currying_Stats;


sub EXPORT is cached {   # do some re-exporting
    my %out = (
        EXPORT => 'dummy',
        Lambda::P6Currying_common::,
        Lambda::P6Currying_X::,
        Lambda::P6Currying_Stats::,
    ).grep(*.key ne 'EXPORT');
    #note "re-exporting {%out.keys}";
    return %out;
}


role Curried {...}
role Partial {...}


my proto sub apply_comp(|) {*}

my multi sub apply_comp($self, Callable     $result)            { curry($result)            }
my multi sub apply_comp($self, Curried      $result) is default { $result                   }
my multi sub apply_comp($self, Unapplicable $result)            { $result                   }
my multi sub apply_comp($self,              $result)            { $result does Unapplicable }


my proto sub apply_more(|) {*}

my multi sub apply_more($self, Callable     $f, @rest)            {              curry($f).invoke(|@rest) }
my multi sub apply_more($self, Curried      $f, @rest) is default {                     $f.invoke(|@rest) }
my multi sub apply_more($self, Unapplicable $f, @rest)            {                     $f.invoke(|@rest) }
my multi sub apply_more($self,              $f, @rest)            { ($f does Unapplicable).invoke(|@rest) }


my sub apply_part(&self, Mu $do, *@args) {
    my @types = types(&self, +@args);
    my $out;
    given +@types {
        when 2 { $out = { $do(|@args, $^b)                      } }
        when 3 { $out = { $do(|@args, $^b, $^c)                 } }
        when 4 { $out = { $do(|@args, $^b, $^c, $^d)            } }
        when 5 { $out = { $do(|@args, $^b, $^c, $^d, $^e)       } }
        when 6 { $out = { $do(|@args, $^b, $^c, $^d, $^e, $^f)  } }
    };
    $out does Partial[|@types];
    $out.name = stats-key(&self) ~ "({+@args}/{&self.arity})";
    return $out;
}


my role Partial[::T1, ::TR] does Curried[T1, TR] {
    has Str $.name is rw;
    has Signature $!s;
    method signature { $!s //= EVAL ":(T1 -->TR)" }
}

my role Partial[::T1, ::T2, ::TR] does Curried[T1, T2, TR] {
    has Str $.name is rw;
    has Signature $!s;
    method signature { $!s //= EVAL ":(T1, T2 -->TR)" }
}

my role Partial[::T1, ::T2, ::T3, ::TR] does Curried[T1, T2, T3, TR] {
    has Str $.name is rw;
    has Signature $!s;
    method signature { $!s //= EVAL ":(T1, T2, T3 -->TR)" }
}

my role Partial[::T1, ::T2, ::T3, ::T4, ::TR] does Curried[T1, T2, T3, T4, TR] {
    has Str $.name is rw;
    has Signature $!s;
    method signature { $!s //= EVAL ":(T1, T2, T3, T4 -->TR)" }
}

my role Partial[::T1, ::T2, ::T3, ::T4, ::T5, ::TR] does Curried[T1, T2, T3, T4, T5, TR] {
    has Str $.name is rw;
    has Signature $!s;
    method signature { $!s //= EVAL ":(T1, T2, T3, T4, T5 -->TR)" }
}

my role Partial[::T1, ::T2, ::T3, ::T4, ::T5, ::T6, ::TR] does Curried[T1, T2, T3, T4, T5, T6, TR] {
    has Str $.name is rw;
    has Signature $!s;
    method signature { $!s //= EVAL ":(T1, T2, T3, T4, T5, T6 -->TR)" }
}

# arity 1
role Curried[::T1, ::TR] {
    has &!do = nqp::getattr(nqp::decont(self), Code, '$!do');

    multi method invoke(T1 $a1                               , *% ()) { apply_comp(self, &!do( $a1)    ) }
    multi method invoke(T1 $a1, *@_ ($, *@)                  , *% ()) { apply_more(self, &!do( $a1), @_) }

    multi method invoke(|as) { dieInvalidArgs(self, as) }

    multi method invoke(Capture:D $as) { self.invoke(|$as) }  # TODO: remove once Rakudo* 2015-02 has landed
}


# arity 2
role Curried[::T1, ::T2, ::TR] {
    has &!do = nqp::getattr(nqp::decont(self), Code, '$!do');

    multi method invoke(T1 $a1                               , *% ()) { apply_part(self, &!do, $a1          ) }
    multi method invoke(T1 $a1, T2 $a2                       , *% ()) { apply_comp(self, &!do( $a1, $a2)    ) }
    multi method invoke(T1 $a1, T2 $a2, *@_ ($, *@)          , *% ()) { apply_more(self, &!do( $a1, $a2), @_) }

    multi method invoke(|as) { dieInvalidArgs(self, as) }

    multi method invoke(Capture:D $as) { self.invoke(|$as) }  # TODO: remove once Rakudo* 2015-02 has landed
}


# arity 3
role Curried[::T1, ::T2, ::T3, ::TR] {
    has &!do = nqp::getattr(nqp::decont(self), Code, '$!do');

    multi method invoke(T1 $a1                               , *% ()) { apply_part(self, &!do, $a1               ) }
    multi method invoke(T1 $a1, T2 $a2                       , *% ()) { apply_part(self, &!do, $a1, $a2          ) }
    multi method invoke(T1 $a1, T2 $a2, T3 $a3               , *% ()) { apply_comp(self, &!do( $a1, $a2, $a3)    ) }
    multi method invoke(T1 $a1, T2 $a2, T3 $a3, *@_ ($, *@)  , *% ()) { apply_more(self, &!do( $a1, $a2, $a3), @_) }

    multi method invoke(|as) { dieInvalidArgs(self, as) }

    multi method invoke(Capture:D $as) { self.invoke(|$as) }  # TODO: remove once Rakudo* 2015-02 has landed
}


# arity 4
role Curried[::T1, ::T2, ::T3, ::T4, ::TR] {
    has &!do = nqp::getattr(nqp::decont(self), Code, '$!do');

    multi method invoke(T1 $a1                                     , *% ()) { apply_part(self, &!do, $a1                    ) }
    multi method invoke(T1 $a1, T2 $a2                             , *% ()) { apply_part(self, &!do, $a1, $a2               ) }
    multi method invoke(T1 $a1, T2 $a2, T3 $a3                     , *% ()) { apply_part(self, &!do, $a1, $a2, $a3          ) }
    multi method invoke(T1 $a1, T2 $a2, T3 $a3, T4 $a4             , *% ()) { apply_comp(self, &!do( $a1, $a2, $a3, $a4)    ) }
    multi method invoke(T1 $a1, T2 $a2, T3 $a3, T4 $a4, *@_ ($, *@), *% ()) { apply_more(self, &!do( $a1, $a2, $a3, $a4), @_) }

    multi method invoke(|as) { dieInvalidArgs(self, as) }

    multi method invoke(Capture:D $as) { self.invoke(|$as) }  # TODO: remove once Rakudo* 2015-02 has landed
}


# arity 5
role Curried[::T1, ::T2, ::T3, ::T4, ::T5, ::TR] {
    has &!do = nqp::getattr(nqp::decont(self), Code, '$!do');

    multi method invoke(T1 $a1                                             , *% ()) { apply_part(self, &!do, $a1                         ) }
    multi method invoke(T1 $a1, T2 $a2                                     , *% ()) { apply_part(self, &!do, $a1, $a2                    ) }
    multi method invoke(T1 $a1, T2 $a2, T3 $a3                             , *% ()) { apply_part(self, &!do, $a1, $a2, $a3               ) }
    multi method invoke(T1 $a1, T2 $a2, T3 $a3, T4 $a4                     , *% ()) { apply_part(self, &!do, $a1, $a2, $a3, $a4          ) }
    multi method invoke(T1 $a1, T2 $a2, T3 $a3, T4 $a4, T5 $a5             , *% ()) { apply_comp(self, &!do( $a1, $a2, $a3, $a4, $a5)    ) }
    multi method invoke(T1 $a1, T2 $a2, T3 $a3, T4 $a4, T5 $a5, *@_ ($, *@), *% ()) { apply_more(self, &!do( $a1, $a2, $a3, $a4, $a5), @_) }

    multi method invoke(|as) { dieInvalidArgs(self, as) }

    multi method invoke(Capture:D $as) { self.invoke(|$as) }  # TODO: remove once Rakudo* 2015-02 has landed
}


# arity 6
role Curried[::T1, ::T2, ::T3, ::T4, ::T5, ::T6, ::TR] {
    has &!do = nqp::getattr(nqp::decont(self), Code, '$!do');

    multi method invoke(T1 $a1                                                     , *% ()) { apply_part(self, &!do, $a1                              ) }
    multi method invoke(T1 $a1, T2 $a2                                             , *% ()) { apply_part(self, &!do, $a1, $a2                         ) }
    multi method invoke(T1 $a1, T2 $a2, T3 $a3                                     , *% ()) { apply_part(self, &!do, $a1, $a2, $a3                    ) }
    multi method invoke(T1 $a1, T2 $a2, T3 $a3, T4 $a4                             , *% ()) { apply_part(self, &!do, $a1, $a2, $a3, $a4               ) }
    multi method invoke(T1 $a1, T2 $a2, T3 $a3, T4 $a4, T5 $a5                     , *% ()) { apply_comp(self, &!do( $a1, $a2, $a3, $a4, $a5)         ) }
    multi method invoke(T1 $a1, T2 $a2, T3 $a3, T4 $a4, T5 $a5, T6 $a6             , *% ()) { apply_comp(self, &!do( $a1, $a2, $a3, $a4, $a5, $a6)    ) }
    multi method invoke(T1 $a1, T2 $a2, T3 $a3, T4 $a4, T5 $a5, T6 $a6, *@_ ($, *@), *% ()) { apply_more(self, &!do( $a1, $a2, $a3, $a4, $a5, $a6), @_) }

    multi method invoke(|as) { dieInvalidArgs(self, as) }

    multi method invoke(Capture:D $as) { self.invoke(|$as) }  # TODO: remove once Rakudo* 2015-02 has landed
}



sub curry(&f -->Callable) is export {
    return &f
        if &f ~~ Curried;

    my $sig = &f.signature;
    my @ps = $sig.params;
    die "cannot curry fn with optional/slurpy/named/capture or parcel parameters - signature: {$sig.perl}; fn: {&f.gist}"
        if @ps.map({$_.optional || $_.slurpy || $_.named || $_.capture || $_.parcel}).any;

    try {
        return &f does Curried[|@(@ps.map(*.type), $sig.returns)];
    }
    my $err = $!;

    my $arity = $sig.arity;
    die "cannot curry nullary fn - signature: {$sig.perl}; fn: {&f.gist}" 
        if $arity == 0;
    die "NYI: Fn with arity $arity (> 6) - signature: {$sig.perl}; fn: {&f.gist}"
        if $arity > 6;
    die $err;   # whatever it was
}

Lambda::P6Currying_Stats::init(Curried, Partial, curry => &curry, part => &apply_part, full => &apply_comp, over => &apply_more);


our sub set_stats_enabled(Bool $enabled) {
    Lambda::P6Currying_Stats::set_enabled($enabled);
}

#set_stats_enabled(True);
