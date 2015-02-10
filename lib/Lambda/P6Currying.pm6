use v6;



my $overAppCount = 0;
my $partialAppCount = 0;

my sub captureToStr($capture) {
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

    submethod BUILD(:$!whatsInFuncPos, :$!args) {
        $!message = "named args not supported for curried fn {$!whatsInFuncPos.WHICH}; got {self.args}";
    }
}

class X::Typing::ArgBinding is X::Typing is export {
    has Str $.message;
    has     $.whatsInFuncPos;
    has     $!args;
    method  args        { captureToStr($!args)    }

    method  expected    { $!whatsInFuncPos.ty }
    method  got         { self.args }

    submethod BUILD(:$!whatsInFuncPos, :$!args) {
        $!message = "cannot apply {$!whatsInFuncPos}: {self.expected} to {self.got}";
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

my role Unapplicable {
    method postcircumfix:<( )>($as) {
        die X::Typing::Unapplicable.new(:whatsInFuncPos(self), :args($as));
    }
    method _(|as) is hidden_from_backtrace {
        self.(|as.list);
    }
}

class Fn { ... }

# This one expects to receive *less than* the args which the orig fn &f expects.
my sub partialApp(&f, *@as) {
    $partialAppCount++;
    #warn ">>>> partial app $partialAppCount:" ~ Backtrace.new;
    my $out = Fn.new(&f, |@as);
    &f.?onPartialApp($out, |@as);
    return $out;
}

# This one expects to receive *exactly* the args which the orig fn &f expects.
my sub completeApp($result) {
    return curry($result)
        if $result ~~ Callable;

    $result does Unapplicable
        unless $result ~~ Unapplicable;
    
    return $result;
}


# Partial0
role Partial0[&f, ::T0, ::R] {
    multi method _(T0 $a0) {                                    completeApp(&f($a0))                     }

    method arity { 1 }
    method count { 1 }
    method sig   { @(T0, R) }
    method ty    { "{T0.perl} -> {R.perl}" }    #    self.sig.map(*.perl).join(' -> ') }     #     
}
role Partial0[&f, ::T0, ::T1, ::R] {
    multi method _(T0 $a0) {                                    partialApp(&f, $a0)                      }
    multi method _(T0 $a0, T1 $a1) {                            completeApp(&f($a0, $a1))                }

    method arity { 2 }
    method count { 2 }
    method sig   { @(T0, T1, R) }
    method ty    { "{T0.perl} -> {T1.perl} -> {R.perl}" }    #    self.sig.map(*.perl).join(' -> ') }     #     
}
role Partial0[&f, ::T0, ::T1, ::T2, ::R] {
    multi method _(T0 $a0) {                                    partialApp(&f, $a0)                      }
    multi method _(T0 $a0, T1 $a1) {                            partialApp(&f, $a0, $a1)                 }
    multi method _(T0 $a0, T1 $a1, T2 $a2) {                    completeApp(&f($a0, $a1, $a2))           }

    method arity { 3 }
    method count { 3 }
    method sig   { @(T0, T1, T2, R) }
    method ty    { "{T0.perl} -> {T1.perl} -> {T2.perl} -> {R.perl}" }    #    self.sig.map(*.perl).join(' -> ') }     #     
}
role Partial0[&f, ::T0, ::T1, ::T2, ::T3, ::R] {
    multi method _(T0 $a0) {                                    partialApp(&f, $a0)                      }
    multi method _(T0 $a0, T1 $a1) {                            partialApp(&f, $a0, $a1)                 }
    multi method _(T0 $a0, T1 $a1, T2 $a2) {                    partialApp(&f, $a0, $a1, $a2)            }
    multi method _(T0 $a0, T1 $a1, T2 $a2, T3 $a3) {            completeApp(&f($a0, $a1, $a2, $a3))      }

    method arity { 4 }
    method count { 4 }
    method sig   { @(T0, T1, T2, T3, R) }
    method ty    { "{T0.perl} -> {T1.perl} -> {T2.perl} -> {T3.perl} -> {R.perl}" }    #    self.sig.map(*.perl).join(' -> ') }     #     
}
role Partial0[&f, ::T0, ::T1, ::T2, ::T3, ::T4, ::R] {
    multi method _(T0 $a0) {                                    partialApp(&f, $a0)                      }
    multi method _(T0 $a0, T1 $a1) {                            partialApp(&f, $a0, $a1)                 }
    multi method _(T0 $a0, T1 $a1, T2 $a2) {                    partialApp(&f, $a0, $a1, $a2)            }
    multi method _(T0 $a0, T1 $a1, T2 $a2, T3 $a3) {            partialApp(&f, $a0, $a1, $a2, $a3)       }
    multi method _(T0 $a0, T1 $a1, T2 $a2, T3 $a3, T4 $a4) {    completeApp((&f, $a0, $a1, $a2, $a3, $a4)) }

    method arity { 5 }
    method count { 5 }
    method sig   { @(T0, T1, T2, T3, T4, R) }
    method ty    { "{T0.perl} -> {T1.perl} -> {T2.perl} -> {T3.perl} -> {T4.perl} -> {R.perl}" }    #    self.sig.map(*.perl).join(' -> ') }     #     
}

# Partial1
role Partial1[&f, $a0, ::T1, ::R] {
    multi method _(T1 $a1) {                                    completeApp(&f($a0, $a1))                }

    method arity { 1 }
    method count { 1 }
    method sig   { @(T1, R) }
    method ty    { "{T1.perl} -> {R.perl}" }    #    self.sig.map(*.perl).join(' -> ') }     #     
}
role Partial1[&f, $a0, ::T1, ::T2, ::R] {
    multi method _(T1 $a1) {                                    partialApp(&f, $a0, $a1)                 }
    multi method _(T1 $a1, T2 $a2) {                            completeApp(&f($a0, $a1, $a2))           }

    method arity { 2 }
    method count { 2 }
    method sig   { @(T1, T2, R) }
    method ty    { "{T1.perl} -> {T2.perl} -> {R.perl}" }    #    self.sig.map(*.perl).join(' -> ') }     #     
}
role Partial1[&f, $a0, ::T1, ::T2, ::T3, ::R] {
    multi method _(T1 $a1) {                                    partialApp(&f, $a0, $a1)                 }
    multi method _(T1 $a1, T2 $a2) {                            partialApp(&f, $a0, $a1, $a2)            }
    multi method _(T1 $a1, T2 $a2, T3 $a3) {                    completeApp(&f($a0, $a1, $a2, $a3))      }

    method arity { 3 }
    method count { 3 }
    method sig   { @(T1, T2, T3, R) }
    method ty    { "{T1.perl} -> {T2.perl} -> {T3.perl} -> {R.perl}" }    #    self.sig.map(*.perl).join(' -> ') }     #     
}
role Partial1[&f, $a0, ::T1, ::T2, ::T3, ::T4, ::R] {
    multi method _(T1 $a1) {                                    partialApp(&f, $a0, $a1)                 }
    multi method _(T1 $a1, T2 $a2) {                            partialApp(&f, $a0, $a1, $a2)            }
    multi method _(T1 $a1, T2 $a2, T3 $a3) {                    partialApp(&f, $a0, $a1, $a2, $a3)       }
    multi method _(T1 $a1, T2 $a2, T3 $a3, T4 $a4) {            completeApp(&f($a0, $a1, $a2, $a3, $a4)) }

    method arity { 4 }
    method count { 4 }
    method sig   { @(T1, T2, T3, T4, R) }
    method ty    { "{T1.perl} -> {T2.perl} -> {T3.perl} -> {T4.perl} -> {R.perl}" }    #    self.sig.map(*.perl).join(' -> ') }     #     
}

# Partial2
role Partial2[&f, $a0, $a1, ::T2, ::R] {
    multi method _(T2 $a2) {                                    completeApp(&f($a0, $a1, $a2))           }

    method arity { 1 }
    method count { 1 }
    method sig   { @(T2, R) }
    method ty    { "{T2.perl} -> {R.perl}" }    #    self.sig.map(*.perl).join(' -> ') }     #     
}
role Partial2[&f, $a0, $a1, ::T2, ::T3, ::R] {
    multi method _(T2 $a2) {                                    partialApp(&f, $a0, $a1, $a2)            }
    multi method _(T2 $a2, T3 $a3) {                            completeApp(&f($a0, $a1, $a2, $a3))      }

    method arity { 2 }
    method count { 2 }
    method sig   { @(T2, T3, R) }
    method ty    { "{T2.perl} -> {T3.perl} -> {R.perl}" }    #    self.sig.map(*.perl).join(' -> ') }     #     
}
role Partial2[&f, $a0, $a1, ::T2, ::T3, ::T4, ::R] {
    multi method _(T2 $a2) {                                    partialApp(&f, $a0, $a1, $a2)            }
    multi method _(T2 $a2, T3 $a3) {                            partialApp(&f, $a0, $a1, $a2, $a3)       }
    multi method _(T2 $a2, T3 $a3, T4 $a4) {                    completeApp(&f($a0, $a1, $a2, $a3, $a4)) }

    method arity { 3 }
    method count { 3 }
    method sig   { @(T2, T3, T4, R) }
    method ty    { "{T2.perl} -> {T3.perl} -> {T4.perl} -> {R.perl}" }    #    self.sig.map(*.perl).join(' -> ') }     #     
}

# Partial3
role Partial3[&f, $a0, $a1, $a2, ::T3, ::R] {
    multi method _(T3 $a3) {                                    completeApp(&f($a0, $a1, $a2, $a3))      }

    method arity { 1 }
    method count { 1 }
    method sig   { @(T3, R) }
    method ty    { "{T3.perl} -> {R.perl}" }    #    self.sig.map(*.perl).join(' -> ') }     #     
}
role Partial3[&f, $a0, $a1, $a2, ::T3, ::T4, ::R] {
    multi method _(T3 $a3) {                                    partialApp(&f, $a0, $a1, $a2, $a3)       }
    multi method _(T3 $a3, T4 $a4) {                            completeApp(&f($a0, $a1, $a2, $a3, $a4)) }

    method arity { 2 }
    method count { 2 }
    method sig   { @(T3, T4, R) }
    method ty    { "{T3.perl} -> {T4.perl} -> {R.perl}" }    #    self.sig.map(*.perl).join(' -> ') }     #     
}

# Partial4
role Partial4[&f, $a0, $a1, $a2, $a3, ::T4, ::R] {
    multi method _(T4 $a4) {                                    completeApp(&f($a0, $a1, $a2, $a3, $a4)) }

    method arity { 1 }
    method count { 1 }
    method sig   { @(T4, R) }
    method ty    { "{T4.perl} -> {R.perl}" }    #    self.sig.map(*.perl).join(' -> ') }     #     
}



class Fn does Callable {
    has &.f;
    has @!partialArgs;

    method new(&f, *@partialArgs) {
        if &f ~~ Fn {
            die "FUCK: " ~ &f.?symbol ~ ' ' ~ &f.?lambda ~ ' ' ~ &f.WHICH;
        }
        self.bless(:&f, :@partialArgs)
            or die "mismatch of arity {self.arity} and nr of args {@partialArgs.elems}";
    }

    submethod BUILD(:&!f, :@!partialArgs) {
        my @ps = &!f.signature.params;
        my $arity = @ps.elems;
        die "cannot curry nullary fn - signature: {&!f.signature.perl}; fn: {&!f.gist}" 
            if $arity == 0;
        die "cannot curry fn with optional/slurpy/named/capture or parcel parameters - signature: {&!f.signature.perl}; fn: {&!f.gist}"
            if @ps.map({$_.optional || $_.slurpy || $_.named || $_.capture || $_.parcel}).any;
        die "NYI: Fn with arity $arity (> 5) - signature: {&!f.signature.perl}; fn: {&!f.gist}"
            if $arity > 5;

        my @ts = @ps.map(*.type);
        my ($a0, $a1, $a2, $a3, $a4) = @!partialArgs;
        my ($t0, $t1, $t2, $t3, $t4) = @ts;
        my $r = &!f.signature.returns;
        my $f = &!f;
        given @!partialArgs.elems {
            when 0 {
                given $arity {
                    when 1 { self does Partial0[$f, $t0                    , $r ] }
                    when 2 { self does Partial0[$f, $t0, $t1               , $r ] }
                    when 3 { self does Partial0[$f, $t0, $t1, $t2          , $r ] }
                    when 4 { self does Partial0[$f, $t0, $t1, $t2, $t3     , $r ] }
                    when 5 { self does Partial0[$f, $t0, $t1, $t2, $t3, $t4, $r ] }
                }
            }
            when 1 {
                given $arity {
                    when 2 { self does Partial1[$f, $a0, $t1               , $r ] }
                    when 3 { self does Partial1[$f, $a0, $t1, $t2          , $r ] }
                    when 4 { self does Partial1[$f, $a0, $t1, $t2, $t3     , $r ] }
                    when 5 { self does Partial1[$f, $a0, $t1, $t2, $t3, $t4, $r ] }
                }
            }
            when 2 {
                given $arity {
                    when 3 { self does Partial2[$f, $a0, $a1, $t2          , $r ] }
                    when 4 { self does Partial2[$f, $a0, $a1, $t2, $t3     , $r ] }
                    when 5 { self does Partial2[$f, $a0, $a1, $t2, $t3, $t4, $r ] }
                }
            }
            when 3 {
                given $arity {
                    when 4 { self does Partial3[$f, $a0, $a1, $a2, $t3     , $r ] }
                    when 5 { self does Partial3[$f, $a0, $a1, $a2, $t3, $t4, $r ] }
                }
            }
            when 4 {
                given $arity {
                    when 5 { self does Partial4[$f, $a0, $a1, $a2, $t3, $t4, $r ] }
                }
            }
        }
    }

    # Dispatch to one of the _ methods from role PartialX 
    # NOTE: doesn't work with postcircumfix:<( )> overrides there, for some reason...?!
    method postcircumfix:<( )>($as) is hidden_from_backtrace {
        die X::Typing::UnsupportedNamedArgs.new(:whatsInFuncPos(self), :args($as))
            unless $as.hash.elems == 0;
        self._(|$as);
    }

    # Fallback, if none of the _ methods from role PartialX matches.
    # Here, *additional* args arrive (to be appended to @!partialArgs).
    # NOT to be used from outside - use normal postcircumfix<( )> instead!
    multi method _(|as) is hidden_from_backtrace {
        my $arity = self.arity; # orig fn's arity - # of @!partialArgs
        my $argCount = as.list.elems;
        if $argCount > $arity {
            $overAppCount++;
            #warn ">>>> over-app $overAppCount: " ~ self ~ Backtrace.new;   #   ;  #   
            #say "n=$n, partialArgs={@!partialArgs.perl}, as={as.perl}";
            my $k = 0;
            my $n = $arity;
            my $result = self;
            loop {
                $result = $result._(|as.list[$k..$n-1]);
                $k = $n;
                $n += $result.?arity // last;
                last if $n >= $argCount;
            };
            $result = $result._(|as.list[$k..*]);
            return $result;
            #my $result = self._(|as.list[0..$arity-1]);
            #my $finalResult = $result(|as.list[$arity..*]);
            #return $finalResult;
        } else {
            my @expectedTypes = self.sig[0..*-2];
            #say (@expectedTypes Z as.list).map(-> $t, $a { "{$t.perl}: {$a.perl}\n" });

            die X::Typing::ArgBinding.new(:whatsInFuncPos(self), :args(as));
        }
    }

}

role Func[::T, ::R] {

    method fnType {
        my $t = T.?fnType // T.WHICH;
        $t = "($t)" if T ~~ Func;
        $t ~ ' -> ' ~ (R.?fnType // R.WHICH)
    }
}

sub curry(&f) is export {
    &f ~~ Fn
        ?? &f
        !! Fn.new(&f);
}
