use v6;


my $nApp_c = 0; # "complete" application
my $nApp_o = 0; # "over-" application
my $nApp_p = 0; # "partial" application

my role CurryStats {
    method gist { self.Str }
    method Str {
        "CurryStats: {self<partial>}p, {self<over>}o, {self<complete>}c";
    }
}

sub curryStats is export {
    { partial => $nApp_p,
      complete => $nApp_c,
      over => $nApp_p
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

my sub typeof(&f) is export {
    my $s = &f.signature;
    @($s.params.map(*.type), $s.returns).map(*.perl).join(' -> ');
}


# This one expects to receive *exactly* the args which the orig fn &f expects.
my sub apply_comp($result) is hidden_from_backtrace {
    return curry($result)
        if $result ~~ Callable;

    $result does Unapplicable
        unless $result ~~ Unapplicable;
    
    return $result;
}

# This one expects to receive *more* args than the orig fn &f expects.
my sub apply_more(&f, @as, @bs) {
    $nApp_o++;
    apply_comp(&f(|@as))._(|@bs);
}

# This one expects to receive *more* args than the orig fn &f expects.
my sub __apply_more(&f, @as, @bs) {

    #warn ">>>> over-app $nApp_o: " ~ self ~ Backtrace.new;   #   ;  #   
    #say "n=$n, partialArgs={@partialArgs.perl}, as={as.perl}";
    my $argCount = @bs.elems;

    my $result = apply_comp(&f(|@as));
    $nApp_o++;
    my $k = 0;
    my $n = $result.?arity // $result(|@bs);    # throws X::Typing::Unapplicable
    while ($n < $argCount) {
        $result = $result._(|@bs[$k..$n-1]); # TODO: use the fact that these are all complete applications
        $k = $n;
        $n += $result.?arity // last;
    }

    $result = $result._(|@bs[$k..*]);    # this may be a partial application
    return $result;
}


# gets called if none of the _ signatures matches (~> invalid call)
my sub dieArgBinding($self, Capture:D $args) is hidden_from_backtrace {
    die X::Typing::ArgBinding.new($self, $args)
}

my sub dieNamedArgs($self, Capture:D $args) is hidden_from_backtrace {
    die X::Typing::UnsupportedNamedArgs.new($self, $args)
}

role Curried is export {...}

role Curried[::T1, ::T2, ::R] {
    
}

role Curried[::T1, ::T2, ::R] {
    
}


# arity 1
role C1[::T1, ::TR] {
    has &.do = nqp::getattr(nqp::decont(self), Code, '$!do');
    has $!T1 = T1;
    has $!TR = TR;

    has Signature $!s;
    method signature { $!s // $!s = (EVAL ":(T1 -->TR)") }

    multi method invoke(T1 $a1                               , *%()) { $nApp_c++; apply_comp(&!do($a1))                                       }
    multi method invoke(T1 $a1, *@_($, *@)                   , *%()) { $nApp_o++; apply_comp(&!do($a1)).invoke(|@_)                           }
    multi method invoke(|as                                        ) { ?as.hash and dieNamedArgs(self, as) or dieArgBinding(self, as)         }

    multi method invoke(Capture:D $as) { self.invoke(|$as) }  # TODO: remove once Rakudo* 2015-02 has landed
}


# arity 2
role C2[::T1, ::T2, ::TR] {
    has &.do = nqp::getattr(nqp::decont(self), Code, '$!do');
    has $!T1 = T1;
    has $!T2 = T2;
    has $!TR = TR;

    has Signature $!s;
    method signature { $!s // ($!s := EVAL ":(T1, T2 -->TR)") }

    multi method invoke(T1 $a1                               , *%()) { $nApp_p++; ({ &!do($a1, $^b) } does C1[$!T2, $!TR])              }
    multi method invoke(T1 $a1, T2 $a2                       , *%()) { $nApp_c++; apply_comp(&!do($a1, $a2))                                  }
    multi method invoke(T1 $a1, T2 $a2, *@_($, *@)           , *%()) { $nApp_o++; apply_comp(&!do($a1, $a2)).invoke(|@_)                      }
    multi method invoke(|as                                        ) { ?as.hash and dieNamedArgs(self, as) or dieArgBinding(self, as)         }

    multi method invoke(Capture:D $as) { self.invoke(|$as) }  # TODO: remove once Rakudo* 2015-02 has landed
}


# arity 3
role C3[::T1, ::T2, ::T3, ::TR] {
    has &.do = nqp::getattr(nqp::decont(self), Code, '$!do');
    has $!T1 = T1;
    has $!T2 = T2;
    has $!T3 = T3;
    has $!TR = TR;

    has Signature $!s;
    method signature { $!s // ($!s := EVAL ":(T1, T2, T3 -->TR)") }

    multi method invoke(T1 $a1                               , *%()) { $nApp_p++; { &!do($a1, $^b, $^c) } does C2[$!T2, $!T3, $!TR]     }
    multi method invoke(T1 $a1, T2 $a2                       , *%()) { $nApp_p++; { &!do($a1, $a2, $^c) } does C1[      $!T3, $!TR]     }
    multi method invoke(T1 $a1, T2 $a2, T3 $a3               , *%()) { $nApp_c++; apply_comp(&!do($a1, $a2, $a3))                             }
    multi method invoke(T1 $a1, T2 $a2, T3 $a3, *@_($, *@)   , *%()) { $nApp_o++; apply_comp(&!do($a1, $a2, $a3)).invoke(|@_)                 }
    multi method invoke(|as                                        ) { ?as.hash and dieNamedArgs(self, as) or dieArgBinding(self, as)         }

    multi method invoke(Capture:D $as) { self.invoke(|$as) }  # TODO: remove once Rakudo* 2015-02 has landed
}


# arity 4
role C4[::T1, ::T2, ::T3, ::T4, ::TR] {
    has &.do = nqp::getattr(nqp::decont(self), Code, '$!do');
    has $!T1 = T1;
    has $!T2 = T2;
    has $!T3 = T3;
    has $!T4 = T4;
    has $!TR = TR;

    has Signature $!s;
    method signature { $!s // ($!s := EVAL ":(T1, T2, T3, T4 -->TR)") }

    multi method invoke(T1 $a1                                    , *%()) { $nApp_p++; { &!do($a1, $^b, $^c, $^d) } does C3[$!T2, $!T3, $!T4, $!TR]   }
    multi method invoke(T1 $a1, T2 $a2                            , *%()) { $nApp_p++; { &!do($a1, $a2, $^c, $^d) } does C2[      $!T3, $!T4, $!TR]   }
    multi method invoke(T1 $a1, T2 $a2, T3 $a3                    , *%()) { $nApp_p++; { &!do($a1, $a2, $a3, $^d) } does C1[            $!T4, $!TR]   }
    multi method invoke(T1 $a1, T2 $a2, T3 $a3, T4 $a4            , *%()) { $nApp_c++; apply_comp(&!do($a1, $a2, $a3, $a4))                                 }
    multi method invoke(T1 $a1, T2 $a2, T3 $a3, T4 $a4, *@_($, *@), *%()) { $nApp_o++; apply_comp(&!do($a1, $a2, $a3, $a4)).invoke(|@_)                     }
    multi method invoke(|as                                             ) { ?as.hash and dieNamedArgs(self, as) or dieArgBinding(self, as)                  }

    multi method invoke(Capture:D $as) { self.invoke(|$as) }  # TODO: remove once Rakudo* 2015-02 has landed
}


# arity 5
role C5[::T1, ::T2, ::T3, ::T4, ::T5, ::TR] {
    has &.do = nqp::getattr(nqp::decont(self), Code, '$!do');
    has $!T1 = T1;
    has $!T2 = T2;
    has $!T3 = T3;
    has $!T4 = T4;
    has $!T5 = T5;
    has $!TR = TR;

    has Signature $!s;
    method signature { $!s // ($!s := EVAL ":(T1, T2, T3, T4, T5 -->TR)") }

    multi method invoke(T1 $a1                                            , *%()) { $nApp_p++; { &!do($a1, $^b, $^c, $^d, $^e) } does C4[$!T2, $!T3, $!T4, $!T5, $!TR]}
    multi method invoke(T1 $a1, T2 $a2                                    , *%()) { $nApp_p++; { &!do($a1, $a2, $^c, $^d, $^e) } does C3[      $!T3, $!T4, $!T5, $!TR]}
    multi method invoke(T1 $a1, T2 $a2, T3 $a3                            , *%()) { $nApp_p++; { &!do($a1, $a2, $a3, $^d, $^e) } does C2[            $!T4, $!T5, $!TR]}
    multi method invoke(T1 $a1, T2 $a2, T3 $a3, T4 $a4                    , *%()) { $nApp_p++; { &!do($a1, $a2, $a3, $a4, $^e) } does C1[                  $!T5, $!TR]}
    multi method invoke(T1 $a1, T2 $a2, T3 $a3, T4 $a4, T5 $a5            , *%()) { $nApp_c++; apply_comp(&!do($a1, $a2, $a3, $a4, $a5))                                    }
    multi method invoke(T1 $a1, T2 $a2, T3 $a3, T4 $a4, T5 $a5, *@_($, *@), *%()) { $nApp_o++; apply_comp(&!do($a1, $a2, $a3, $a4, $a5)).invoke(|@_)                        }

    multi method invoke(|as) { ?as.hash and dieNamedArgs(self, as) or dieArgBinding(self, as) }
    multi method invoke(Capture:D $as) { self.invoke(|$as) }  # TODO: remove once Rakudo* 2015-02 has landed
}



my sub _curry(&f -->Callable) {
    my $sig = &f.signature;
    my $arity = $sig.arity;
    my $r = $sig.returns;
    my ($t1, $t2, $t3, $t4, $t5) = $sig.params.map(*.type);
    given $arity {
        when 1 { &f does C1[$t1                    , $r] }
        when 2 { &f does C2[$t1, $t2               , $r] }
        when 3 { &f does C3[$t1, $t2, $t3          , $r] }
        when 4 { &f does C4[$t1, $t2, $t3, $t4     , $r] }
        when 5 { &f does C5[$t1, $t2, $t3, $t4, $t5, $r] }
    }
}

class Fn does Callable {

}

role Func[::T, ::R] {

    method fnType {
        my $t = T.?fnType // T.WHICH;
        $t = "($t)" if T ~~ Func;
        $t ~ ' -> ' ~ (R.?fnType // R.WHICH)
    }
}

sub curry(&f) is export {
    return &f
        if (&f ~~ C1)
        || (&f ~~ C2)
        || (&f ~~ C3)
        || (&f ~~ C4)
        || (&f ~~ C5)
    ;

    my @ps = &f.signature.params;
    my $arity = @ps.elems;
    die "cannot curry nullary fn - signature: {&f.signature.perl}; fn: {&f.gist}" 
        if $arity == 0;
    die "cannot curry fn with optional/slurpy/named/capture or parcel parameters - signature: {&f.signature.perl}; fn: {&f.gist}"
        if @ps.map({$_.optional || $_.slurpy || $_.named || $_.capture || $_.parcel}).any;
    die "NYI: Fn with arity $arity (> 5) - signature: {&f.signature.perl}; fn: {&f.gist}"
        if $arity > 5;

    return _curry(&f);
}

#`{
my $f = sub (Str $x, Int $y -->Str) {$x x $y};
my $fc = curry($f);

say $fc.WHICH;
say $fc.WHAT;
say $fc.WHERE;
say $fc.signature;
my @ms = $fc.^find_method('invoke').candidates\
    .grep(*.count == $fc.count + 1)\
    .map(*.signature.params)\
    .grep(!*.invocant)\
    .grep(!*.slurpy)
;
say "{+@ms}: " ~ @ms.perl;
say '';

my $g = $fc("foo");
say $g.WHICH;
say $g.signature;
say '';

my $h = $fc("foo", 3);
say $h;
say $h.signature;

#say $fc('baz', foo => 'bar');
##say $fc._(foo => 'bar');
}