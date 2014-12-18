use v6;

# Partial0

role Partial0[::T0] {
    multi method _(T0:D $a0) {                                  self.apply($a0)                }
}

role Partial0[::T0, ::T1] {
    multi method _(T0:D $a0) {                                  self.apply($a0)                }
    multi method _(T0:D $a0, T1:D $a1) {                        self.apply($a0, $a1)           }
}

role Partial0[::T0, ::T1, ::T2] {
    multi method _(T0:D $a0) {                                  self.apply($a0)                }
    multi method _(T0:D $a0, T1:D $a1) {                        self.apply($a0, $a1)           }
    multi method _(T0:D $a0, T1:D $a1, T2:D $a2) {              self.apply($a0, $a1, $a2)      }
}

role Partial0[::T0, ::T1, ::T2, ::T3] {
    multi method _(T0:D $a0) {                                  self.apply($a0)                }
    multi method _(T0:D $a0, T1:D $a1) {                        self.apply($a0, $a1)           }
    multi method _(T0:D $a0, T1:D $a1, T2:D $a2) {              self.apply($a0, $a1, $a2)      }
    multi method _(T0:D $a0, T1:D $a1, T2:D $a2, T3:D $a3) {    self.apply($a0, $a1, $a2, $a3) }
}


# Partial1

role Partial1[$a0, ::T1] {
    multi method _(T1:D $a1) {                                  self.apply($a0, $a1)           }
}

role Partial1[$a0, ::T1, ::T2] {
    multi method _(T1:D $a1) {                                  self.apply($a0, $a1)           }
    multi method _(T1:D $a1, T2:D $a2) {                        self.apply($a0, $a1, $a2)      }
}

role Partial1[$a0, ::T1, ::T2, ::T3] {
    multi method _(T1:D $a1) {                                  self.apply($a0, $a1)           }
    multi method _(T1:D $a1, T2:D $a2) {                        self.apply($a0, $a1, $a2)      }
    multi method _(T1:D $a1, T2:D $a2, T3:D $a3) {              self.apply($a0, $a1, $a2, $a3) }
}


# Partial2

role Partial2[$a0, $a1, ::T2] {
    multi method _(T2:D $a2) {                                  self.apply($a0, $a1, $a2)      }
}

role Partial2[$a0, $a1, ::T2, ::T3] {
    multi method _(T2:D $a2) {                                  self.apply($a0, $a1, $a2)      }
    multi method _(T2:D $a2, T3:D $a3) {                        self.apply($a0, $a1, $a2, $a3) }
}


# Partial3

role Partial3[$a0, $a1, $a2, ::T3] {
    multi method _(T3:D $a3) {                                  self.APPLY($a0, $a1, $a2, $a3) }
}


my class Fn does Callable {
    has &.f;

    method new(&f, *@as) {
        self.bless(:&f, :@as)
            or die "mismatch of arity {self.arity} and nr of args {@as.elems}";
    }

    submethod BUILD(:&!f, :@as) {
        my @ts = &!f.signature.params.map(*.type);
        my $arity = @ts.elems;
        die "NYI: Fn with arity > $arity"
            if $arity > 4;

        my ($a0, $a1, $a2, $a3) = @as;
        my ($t0, $t1, $t2, $t3) = @ts;
        given @as.elems {
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

    method signature { &!f.signature }
    method arity     { &!f.signature.arity }

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
    multi method _(|as) {
        die "cannot apply {self.ty} to (" ~ as.list.map(*.WHICH).join(', ') ~ ')';
    }

    # NOT to be used from outside - use normal postcircumfix<( )> instead!
    method apply(*@as) {
        @as == self.arity ?? &!f.(|@as) !! Fn.new(&!f, |@as);
    }
}

sub curry(&f) is export {
    Fn.new(&f);
}