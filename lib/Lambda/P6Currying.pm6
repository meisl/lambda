use v6;

# Partial0
role Partial0[::T0] {
    multi method _(T0 $a0) {                            self.apply($a0)                }
}
role Partial0[::T0, ::T1] {
    multi method _(T0 $a0) {                            self.apply($a0)                }
    multi method _(T0 $a0, T1 $a1) {                    self.apply($a0, $a1)           }
}
role Partial0[::T0, ::T1, ::T2] {
    multi method _(T0 $a0) {                            self.apply($a0)                }
    multi method _(T0 $a0, T1 $a1) {                    self.apply($a0, $a1)           }
    multi method _(T0 $a0, T1 $a1, T2 $a2) {            self.apply($a0, $a1, $a2)      }
}
role Partial0[::T0, ::T1, ::T2, ::T3] {
    multi method _(T0 $a0) {                            self.apply($a0)                }
    multi method _(T0 $a0, T1 $a1) {                    self.apply($a0, $a1)           }
    multi method _(T0 $a0, T1 $a1, T2 $a2) {            self.apply($a0, $a1, $a2)      }
    multi method _(T0 $a0, T1 $a1, T2 $a2, T3 $a3) {    self.apply($a0, $a1, $a2, $a3) }
}

# Partial1
role Partial1[$a0, ::T1] {
    multi method _(T1 $a1) {                            self.apply($a0, $a1)           }
}
role Partial1[$a0, ::T1, ::T2] {
    multi method _(T1 $a1) {                            self.apply($a0, $a1)           }
    multi method _(T1 $a1, T2 $a2) {                    self.apply($a0, $a1, $a2)      }
}
role Partial1[$a0, ::T1, ::T2, ::T3] {
    multi method _(T1 $a1) {                            self.apply($a0, $a1)           }
    multi method _(T1 $a1, T2 $a2) {                    self.apply($a0, $a1, $a2)      }
    multi method _(T1 $a1, T2 $a2, T3 $a3) {            self.apply($a0, $a1, $a2, $a3) }
}

# Partial2
role Partial2[$a0, $a1, ::T2] {
    multi method _(T2 $a2) {                            self.apply($a0, $a1, $a2)      }
}
role Partial2[$a0, $a1, ::T2, ::T3] {
    multi method _(T2 $a2) {                            self.apply($a0, $a1, $a2)      }
    multi method _(T2 $a2, T3 $a3) {                    self.apply($a0, $a1, $a2, $a3) }
}

# Partial3
role Partial3[$a0, $a1, $a2, ::T3] {
    multi method _(T3 $a3) {                            self.apply($a0, $a1, $a2, $a3) }
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
        die "cannot curry nullary fn" 
            if $arity == 0;
        die "cannot curry fn with optional parameters"
            if @ps.map({$_.optional || $_.slurpy || $_.named || $_.capture || $_.parcel}).any;
        die "NYI: Fn with arity > $arity"
            if $arity > 4;

        my @ts = @ps.map(*.type);
        my ($a0, $a1, $a2, $a3) = @!partialArgs;
        my ($t0, $t1, $t2, $t3) = @ts;
        given @!partialArgs.elems {
            when 0 {
                given $arity {
                    when 1 { self does Partial0[$t0                 ] }
                    when 2 { self does Partial0[$t0, $t1            ] }
                    when 3 { self does Partial0[$t0, $t1, $t2       ] }
                    when 4 { self does Partial0[$t0, $t1, $t2, $t3  ] }
                }
            }
            when 1 {
                given $arity {
                    when 2 { self does Partial1[$a0, $t1            ] }
                    when 3 { self does Partial1[$a0, $t1, $t2       ] }
                    when 4 { self does Partial1[$a0, $t1, $t2, $t3  ] }
                }
            }
            when 2 {
                given $arity {
                    when 3 { self does Partial2[$a0, $a1, $t2       ] }
                    when 4 { self does Partial2[$a0, $a1, $t2, $t3  ] }
                }
            }
            when 3 {
                given $arity {
                    when 4 { self does Partial3[$a0, $a1, $a2, $t3  ] }
                }
            }
        }
    }

    method arity { &!f.signature.params.elems - @!partialArgs.elems }
    method count { self.arity }

    method ty {
        my $s = &!f.signature;
        @($s.params.map(*.type), $s.returns).map(*.perl).join(' -> ');
    }

    # dispatch to one of the _ methods from role PartialX 
    # (doesn't work with postcircumfix:<( )> overrides there, for some reason...?)
    multi method postcircumfix:<( )>($as) {
        self._(|$as);
    }

    # fallback, if none of _ methods from role PartialX matches
    multi method _(|as) is hidden_from_backtrace {
        die "cannot apply {self.ty} to (" ~ as.list.map(*.WHICH).join(', ') ~ ')'
    }

    # NOT to be used from outside - use normal postcircumfix<( )> instead!
    method apply(*@as) {
        my $out;
        if @as == &!f.signature.arity {
            $out = &!f.(|@as);
        } else {
            $out = Fn.new(&!f, |@as);
            &!f.?onPartialApp($out, |@as);
        }
        return $out;
    }

}

sub curry(&f) is export {
    &f ~~ Fn
        ?? &f
        !! Fn.new(&f);
}
