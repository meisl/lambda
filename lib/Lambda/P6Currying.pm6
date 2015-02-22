use v6;


my $nApp_c = 0; # "complete" application
my $nApp_o = 0; # "over-" application
my $nApp_p = 0; # "partial" application
my $nCurry = 0; # calls to sub curry (without early exits)
my $nCurry_ttl = 0; # calls to sub curry

my role CurryStats {
    method gist { self.Str }
    method Str {
        "CurryStats: {self<partial>}p, {self<over>}o, {self<complete>}c, {self<curry>}/{self<curry_ttl>}i";
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


# gets called if none of the _ signatures matches (~> invalid call)
my sub dieArgBinding($self, Capture:D $args) is hidden_from_backtrace {
    die X::Typing::ArgBinding.new($self, $args)
}

my sub dieNamedArgs($self, Capture:D $args) is hidden_from_backtrace {
    die X::Typing::UnsupportedNamedArgs.new($self, $args)
}

my sub dieInvalidArgs($self, Capture:D $args) is hidden_from_backtrace {
    ?$args.hash and dieNamedArgs($self, $args) or dieArgBinding($self, $args)
}


my sub typeof(&f) is export {
    my $s = &f.signature;
    @($s.params.map(*.type), $s.returns).map(*.perl).join(' -> ');
}

role Curried {...}


my proto sub apply_comp(|) {*}

my multi sub apply_comp(             &result)            { $nApp_c++; curry(&result)            }  # 460
my multi sub apply_comp(Curried      $result) is default { $nApp_c++; $result                   }  #   0
my multi sub apply_comp(Unapplicable $result)            { $nApp_c++; $result                   }  # 223
my multi sub apply_comp(             $result)            { $nApp_c++; $result does Unapplicable }  #  65


my proto sub apply_more(|) {*}

my multi sub apply_more(             &f, @rest)            { $nApp_o++;              curry(&f).invoke(|@rest) }
my multi sub apply_more(Curried      $f, @rest) is default { $nApp_o++;                     $f.invoke(|@rest) }
my multi sub apply_more(Unapplicable $f, @rest)            { $nApp_o++;                     $f.invoke(|@rest) }
my multi sub apply_more(             $f, @rest)            { $nApp_o++; ($f does Unapplicable).invoke(|@rest) }


my sub apply_part(&self, Mu $do, *@args) {
    $nApp_p++;
    my $n = +@args;
    my $s = &self.signature;
    my &out;
    given $s.arity - $n {
        when 1 { &out = { $do(|@args, $^b)                 } }
        when 2 { &out = { $do(|@args, $^b, $^c)            } }
        when 3 { &out = { $do(|@args, $^b, $^c, $^d)       } }
        when 4 { &out = { $do(|@args, $^b, $^c, $^d, $^e)  } }
    }
    my @types = ($s.params[$n..*].map(*.type), $s.returns);
    return &out does Curried[|@types];
}

# arity 1
role Curried[::T1, ::TR] {
    has &!do = nqp::getattr(nqp::decont(self), Code, '$!do');

    has Signature $!s;
    method signature { $!s // $!s = (EVAL ":(T1 -->TR)") }

    multi method invoke(T1 $a1                               , *%()) { apply_comp(&!do($a1))                                       }
    multi method invoke(T1 $a1, *@_($, *@)                   , *%()) { apply_more(&!do($a1), @_)                           }

    multi method invoke(|as) { dieInvalidArgs(self, as) }

    multi method invoke(Capture:D $as) { self.invoke(|$as) }  # TODO: remove once Rakudo* 2015-02 has landed
}


# arity 2
role Curried[::T1, ::T2, ::TR] {
    has &!do = nqp::getattr(nqp::decont(self), Code, '$!do');

    has Signature $!s;
    method signature { $!s // ($!s := EVAL ":(T1, T2 -->TR)") }

    multi method invoke(T1 $a1                               , *%()) { apply_part(self, &!do, $a1          ) }
    multi method invoke(T1 $a1, T2 $a2                       , *%()) { apply_comp(      &!do( $a1, $a2)    ) }
    multi method invoke(T1 $a1, T2 $a2, *@_($, *@)           , *%()) { apply_more(      &!do( $a1, $a2), @_) }

    multi method invoke(|as) { dieInvalidArgs(self, as) }

    multi method invoke(Capture:D $as) { self.invoke(|$as) }  # TODO: remove once Rakudo* 2015-02 has landed
}


# arity 3
role Curried[::T1, ::T2, ::T3, ::TR] {
    has &!do = nqp::getattr(nqp::decont(self), Code, '$!do');

    has Signature $!s;
    method signature { $!s // ($!s := EVAL ":(T1, T2, T3 -->TR)") }

    multi method invoke(T1 $a1                               , *%()) { apply_part(self, &!do, $a1               ) }
    multi method invoke(T1 $a1, T2 $a2                       , *%()) { apply_part(self, &!do, $a1, $a2          ) }
    multi method invoke(T1 $a1, T2 $a2, T3 $a3               , *%()) { apply_comp(      &!do( $a1, $a2, $a3)    ) }
    multi method invoke(T1 $a1, T2 $a2, T3 $a3, *@_($, *@)   , *%()) { apply_more(      &!do( $a1, $a2, $a3), @_) }

    multi method invoke(|as) { dieInvalidArgs(self, as) }

    multi method invoke(Capture:D $as) { self.invoke(|$as) }  # TODO: remove once Rakudo* 2015-02 has landed
}


# arity 4
role Curried[::T1, ::T2, ::T3, ::T4, ::TR] {
    has &!do = nqp::getattr(nqp::decont(self), Code, '$!do');

    has Signature $!s;
    method signature { $!s // ($!s := EVAL ":(T1, T2, T3, T4 -->TR)") }

    multi method invoke(T1 $a1                                    , *%()) { apply_part(self, &!do, $a1                    ) }
    multi method invoke(T1 $a1, T2 $a2                            , *%()) { apply_part(self, &!do, $a1, $a2               ) }
    multi method invoke(T1 $a1, T2 $a2, T3 $a3                    , *%()) { apply_part(self, &!do, $a1, $a2, $a3          ) }
    multi method invoke(T1 $a1, T2 $a2, T3 $a3, T4 $a4            , *%()) { apply_comp(      &!do( $a1, $a2, $a3, $a4)    ) }
    multi method invoke(T1 $a1, T2 $a2, T3 $a3, T4 $a4, *@_($, *@), *%()) { apply_more(      &!do( $a1, $a2, $a3, $a4), @_) }

    multi method invoke(|as) { dieInvalidArgs(self, as) }

    multi method invoke(Capture:D $as) { self.invoke(|$as) }  # TODO: remove once Rakudo* 2015-02 has landed
}


# arity 5
role Curried[::T1, ::T2, ::T3, ::T4, ::T5, ::TR] {
    has &!do = nqp::getattr(nqp::decont(self), Code, '$!do');

    has Signature $!s;
    method signature { $!s // ($!s := EVAL ":(T1, T2, T3, T4, T5 -->TR)") }

    multi method invoke(T1 $a1                                            , *%()) { apply_part(self, &!do, $a1                         ) }
    multi method invoke(T1 $a1, T2 $a2                                    , *%()) { apply_part(self, &!do, $a1, $a2                    ) }
    multi method invoke(T1 $a1, T2 $a2, T3 $a3                            , *%()) { apply_part(self, &!do, $a1, $a2, $a3               ) }
    multi method invoke(T1 $a1, T2 $a2, T3 $a3, T4 $a4                    , *%()) { apply_part(self, &!do, $a1, $a2, $a3, $a4          ) }
    multi method invoke(T1 $a1, T2 $a2, T3 $a3, T4 $a4, T5 $a5            , *%()) { apply_comp(      &!do( $a1, $a2, $a3, $a4, $a5)    ) }
    multi method invoke(T1 $a1, T2 $a2, T3 $a3, T4 $a4, T5 $a5, *@_($, *@), *%()) { apply_more(      &!do( $a1, $a2, $a3, $a4, $a5), @_) }

    multi method invoke(|as) { dieInvalidArgs(self, as) }

    multi method invoke(Capture:D $as) { self.invoke(|$as) }  # TODO: remove once Rakudo* 2015-02 has landed
}



sub curry(&f -->Callable) is export {
    $nCurry_ttl++;
    return &f
        if &f ~~ Curried;

    $nCurry++;
    my $sig = &f.signature;
    my $arity = $sig.arity;
    die "cannot curry nullary fn - signature: {$sig.perl}; fn: {&f.gist}" 
        if $arity == 0;

    my @ps = $sig.params;
    die "cannot curry fn with optional/slurpy/named/capture or parcel parameters - signature: {$sig.perl}; fn: {&f.gist}"
        if @ps.map({$_.optional || $_.slurpy || $_.named || $_.capture || $_.parcel}).any;

    die "NYI: Fn with arity $arity (> 5) - signature: {$sig.perl}; fn: {&f.gist}"
        if $arity > 5;

    my $out = &f does Curried[|@(@ps.map(*.type), $sig.returns)];

    return $out;
}
