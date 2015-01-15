use v6;

# Partial0
role Partial0[::T0] {
    multi method _(T0 $a0) {                                    self.apply($a0)                     }
}
role Partial0[::T0, ::T1] {
    multi method _(T0 $a0) {                                    self.apply($a0)                     }
    multi method _(T0 $a0, T1 $a1) {                            self.apply($a0, $a1)                }
}
role Partial0[::T0, ::T1, ::T2] {
    multi method _(T0 $a0) {                                    self.apply($a0)                     }
    multi method _(T0 $a0, T1 $a1) {                            self.apply($a0, $a1)                }
    multi method _(T0 $a0, T1 $a1, T2 $a2) {                    self.apply($a0, $a1, $a2)           }
}
role Partial0[::T0, ::T1, ::T2, ::T3] {
    multi method _(T0 $a0) {                                    self.apply($a0)                     }
    multi method _(T0 $a0, T1 $a1) {                            self.apply($a0, $a1)                }
    multi method _(T0 $a0, T1 $a1, T2 $a2) {                    self.apply($a0, $a1, $a2)           }
    multi method _(T0 $a0, T1 $a1, T2 $a2, T3 $a3) {            self.apply($a0, $a1, $a2, $a3)      }
}
role Partial0[::T0, ::T1, ::T2, ::T3, ::T4] {
    multi method _(T0 $a0) {                                    self.apply($a0)                     }
    multi method _(T0 $a0, T1 $a1) {                            self.apply($a0, $a1)                }
    multi method _(T0 $a0, T1 $a1, T2 $a2) {                    self.apply($a0, $a1, $a2)           }
    multi method _(T0 $a0, T1 $a1, T2 $a2, T3 $a3) {            self.apply($a0, $a1, $a2, $a3)      }
    multi method _(T0 $a0, T1 $a1, T2 $a2, T3 $a3, T4 $a4) {    self.apply($a0, $a1, $a2, $a3, $a4) }
}

# Partial1
role Partial1[$a0, ::T1] {
    multi method _(T1 $a1) {                                    self.apply($a0, $a1)                }
}
role Partial1[$a0, ::T1, ::T2] {
    multi method _(T1 $a1) {                                    self.apply($a0, $a1)                }
    multi method _(T1 $a1, T2 $a2) {                            self.apply($a0, $a1, $a2)           }
}
role Partial1[$a0, ::T1, ::T2, ::T3] {
    multi method _(T1 $a1) {                                    self.apply($a0, $a1)                }
    multi method _(T1 $a1, T2 $a2) {                            self.apply($a0, $a1, $a2)           }
    multi method _(T1 $a1, T2 $a2, T3 $a3) {                    self.apply($a0, $a1, $a2, $a3)      }
}
role Partial1[$a0, ::T1, ::T2, ::T3, ::T4] {
    multi method _(T1 $a1) {                                    self.apply($a0, $a1)                }
    multi method _(T1 $a1, T2 $a2) {                            self.apply($a0, $a1, $a2)           }
    multi method _(T1 $a1, T2 $a2, T3 $a3) {                    self.apply($a0, $a1, $a2, $a3)      }
    multi method _(T1 $a1, T2 $a2, T3 $a3, T4 $a4) {            self.apply($a0, $a1, $a2, $a3, $a4) }
}

# Partial2
role Partial2[$a0, $a1, ::T2] {
    multi method _(T2 $a2) {                                    self.apply($a0, $a1, $a2)           }
}
role Partial2[$a0, $a1, ::T2, ::T3] {
    multi method _(T2 $a2) {                                    self.apply($a0, $a1, $a2)           }
    multi method _(T2 $a2, T3 $a3) {                            self.apply($a0, $a1, $a2, $a3)      }
}
role Partial2[$a0, $a1, ::T2, ::T3, ::T4] {
    multi method _(T2 $a2) {                                    self.apply($a0, $a1, $a2)           }
    multi method _(T2 $a2, T3 $a3) {                            self.apply($a0, $a1, $a2, $a3)      }
    multi method _(T2 $a2, T3 $a3, T4 $a4) {                    self.apply($a0, $a1, $a2, $a3, $a4) }
}

# Partial3
role Partial3[$a0, $a1, $a2, ::T3] {
    multi method _(T3 $a3) {                                    self.apply($a0, $a1, $a2, $a3)      }
}
role Partial3[$a0, $a1, $a2, ::T3, ::T4] {
    multi method _(T3 $a3) {                                    self.apply($a0, $a1, $a2, $a3)      }
    multi method _(T3 $a3, T4 $a4) {                            self.apply($a0, $a1, $a2, $a3, $a4) }
}

# Partial4
role Partial4[$a0, $a1, $a2, $a3, ::T4] {
    multi method _(T4 $a4) {                                    self.apply($a0, $a1, $a2, $a3, $a4) }
}



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
        given @!partialArgs.elems {
            when 0 {
                given $arity {
                    when 1 { self does Partial0[$t0                     ] }
                    when 2 { self does Partial0[$t0, $t1                ] }
                    when 3 { self does Partial0[$t0, $t1, $t2           ] }
                    when 4 { self does Partial0[$t0, $t1, $t2, $t3      ] }
                    when 5 { self does Partial0[$t0, $t1, $t2, $t3, $t4 ] }
                }
            }
            when 1 {
                given $arity {
                    when 2 { self does Partial1[$a0, $t1                ] }
                    when 3 { self does Partial1[$a0, $t1, $t2           ] }
                    when 4 { self does Partial1[$a0, $t1, $t2, $t3      ] }
                    when 5 { self does Partial1[$a0, $t1, $t2, $t3, $t4 ] }
                }
            }
            when 2 {
                given $arity {
                    when 3 { self does Partial2[$a0, $a1, $t2           ] }
                    when 4 { self does Partial2[$a0, $a1, $t2, $t3      ] }
                    when 5 { self does Partial2[$a0, $a1, $t2, $t3, $t4 ] }
                }
            }
            when 3 {
                given $arity {
                    when 4 { self does Partial3[$a0, $a1, $a2, $t3      ] }
                    when 5 { self does Partial3[$a0, $a1, $a2, $t3, $t4 ] }
                }
            }
            when 4 {
                given $arity {
                    when 5 { self does Partial4[$a0, $a1, $a2, $t3, $t4 ] }
                }
            }
        }
    }

    method arity { &!f.signature.params.elems - @!partialArgs.elems }
    method count { self.arity }

    method sig {
        my $s = &!f.signature;
        @($s.params[@!partialArgs.elems..*].map(*.type), $s.returns);
    }

    method ty {
        self.sig.map(*.perl).join(' -> ');
    }

    # Dispatch to one of the _ methods from role PartialX 
    # NOTE: doesn't work with postcircumfix:<( )> overrides there, for some reason...?!
    method postcircumfix:<( )>($as) {
        die X::Typing::UnsupportedNamedArgs.new(:whatsInFuncPos(self), :args($as))
            unless $as.hash.elems == 0;
        self._(|$as);
    }

    # Fallback, if none of _ methods from role PartialX matches.
    # Here, *additional* args arrive (to be appended to @!partialArgs).
    # NOT to be used from outside - use normal postcircumfix<( )> instead!
    multi method _(|as) {
        my $n = self.arity; # orig fn's arity - # of @!partialArgs
        if as.list.elems > $n {
            #say "n=$n, partialArgs={@!partialArgs.perl}, as={as.perl}";
            my $myResult = self._(|as.list[0..$n-1]);
            #say '################# ' ~ $myResult.WHICH;
            my $finalResult = $myResult(|as.list[$n..*]);
            return $finalResult;
        } else {
            die X::Typing::ArgBinding.new(:whatsInFuncPos(self), :args(as));
        }
    }

    # This one expects to receive *all of or less than* the args which the orig fn $!f expects.
    # NOT to be used from outside - use normal postcircumfix<( )> instead!
    method apply(*@as) {
        my $out;
        my $n = &!f.signature.arity;
        if @as == $n {
            $out = &!f.(|@as);
        } else { # got *LESS* params (if it were more then we'd ended up in the fallback method _ above)
            $out = Fn.new(&!f, |@as);
            &!f.?onPartialApp($out, |@as);
        }
        if ($out ~~ Callable) && ($out !~~ Unapplicable) { #or $out.^can('postcircumfix:<( )>') {
            $out = curry($out);
        } else {
            $out does Unapplicable
                unless $out ~~ Unapplicable;
        }
        return $out;
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
