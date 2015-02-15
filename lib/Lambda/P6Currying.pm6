use v6;


my $nApp_o = 0;
my $nApp_p = 0;

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

my role Unapplicable {
    multi method postcircumfix:<( )>($as) {
        die X::Typing::Unapplicable.new(:whatsInFuncPos(self), :args($as));
    }
    method _(|as) {    # TODO: why do we need a fallback `_` method in role Unapplicable?
        self.(|as.list);
    }
}

class Fn { ... }

role Partial0of1 { ... }

role Partial0of2 { ... }
role Partial1of2 { ... }

role Partial0of3 { ... }
role Partial1of3 { ... }
role Partial2of3 { ... }

role Partial0of4 { ... }
role Partial1of4 { ... }
role Partial2of4 { ... }
role Partial3of4 { ... }

role Partial0of5 { ... }
role Partial1of5 { ... }
role Partial2of5 { ... }
role Partial3of5 { ... }
role Partial4of5 { ... }

my sub typeStr(@types) {
    @types.map(*.perl).join(' -> ');
}


# This one expects to receive *less than* the args which the orig fn &f expects.
my sub apply_part(&f, *@as) {
    $nApp_p++;
    #warn ">>>> partial app $nApp_p:" ~ Backtrace.new;
    my $out = _curry(&f.clone, &f, :partialArgs(@as));
    &f.?onPartialApp($out, @as);
    return $out;
}

# This one expects to receive *exactly* the args which the orig fn &f expects.
my sub apply_comp($result) {
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

# Dispatch to one of the _ methods from role PartialX 
# NOTE: doesn't work with postcircumfix:<( )> overrides there, for some reason...?!
my sub enter($self, Capture:D $args) {
    die X::Typing::UnsupportedNamedArgs.new(:whatsInFuncPos($self), :$args)
        unless $args.hash.elems == 0;
    $self._(|$args);
}



# arity 1
role Partial0of1[&f, ::T1, ::R] {
    multi method _(T1 $a1                        )            { apply_comp(&f($a1))                     }
    multi method _(T1 $a1, *@bs                  ) is default { apply_more(&f, [$a1], @bs)              }
    multi method _(|as                           )            { die X::Typing::ArgBinding.new(self, as) }
    
    multi method postcircumfix:<( )>($as) {  enter(self, $as)                     }

    method arity { 1 }
    method count { 1 }
    method sig   { @(T1, R) }
    method ty    { typeStr(self.sig) }
}

# arity 2
role Partial0of2[&f, ::T1, ::T2, ::R] {
    multi method _(T1 $a1                        )            { apply_part(&f, $a1)                     }
    multi method _(T1 $a1, T2 $a2                )            { apply_comp(&f($a1, $a2))                }
    multi method _(T1 $a1, T2 $a2, *@bs          ) is default { apply_more(&f, [$a1, $a2], @bs)         }
    multi method _(|as                           )            { die X::Typing::ArgBinding.new(self, as) }
    
    multi method postcircumfix:<( )>($as) {  enter(self, $as)                     }

    method arity { 2 }
    method count { 2 }
    method sig   { @(T1, T2, R) }
    method ty    { typeStr(self.sig) }
}
role Partial1of2[&f, $a1, ::T2, ::R] {
    multi method _(T2 $a2                        )            { apply_comp(&f($a1, $a2))                }
    multi method _(T2 $a2, *@bs                  ) is default { apply_more(&f, [$a1, $a2], @bs)         }
    multi method _(|as                           )            { die X::Typing::ArgBinding.new(self, as) }

    multi method postcircumfix:<( )>($as) {  enter(self, $as)                     }

    method arity { 1 }
    method count { 1 }
    method sig   { @(T2, R) }
    method ty    { typeStr(self.sig) }
}

# arity 3
role Partial0of3[&f, ::T1, ::T2, ::T3, ::R] {
    multi method _(T1 $a1                        )            { apply_part(&f, $a1)                     }
    multi method _(T1 $a1, T2 $a2                )            { apply_part(&f, $a1, $a2)                }
    multi method _(T1 $a1, T2 $a2, T3 $a3        )            { apply_comp(&f($a1, $a2, $a3))           }
    multi method _(T1 $a1, T2 $a2, T3 $a3, *@bs  ) is default { apply_more(&f, [$a1, $a2, $a3], @bs)    }
    multi method _(|as                           )            { die X::Typing::ArgBinding.new(self, as) }
    
    multi method postcircumfix:<( )>($as) {  enter(self, $as)                     }

    method arity { 3 }
    method count { 3 }
    method sig   { @(T1, T2, T3, R) }
    method ty    { typeStr(self.sig) }
}
role Partial1of3[&f, $a1, ::T2, ::T3, ::R] {
    multi method _(T2 $a2                        )            { apply_part(&f, $a1, $a2)                }
    multi method _(T2 $a2, T3 $a3                )            { apply_comp(&f($a1, $a2, $a3))           }
    multi method _(T2 $a2, T3 $a3, *@bs          ) is default { apply_more(&f, [$a1, $a2, $a3], @bs)    }
    multi method _(|as                           )            { die X::Typing::ArgBinding.new(self, as) }

    multi method postcircumfix:<( )>($as) {  enter(self, $as)                     }

    method arity { 2 }
    method count { 2 }
    method sig   { @(T2, T3, R) }
    method ty    { typeStr(self.sig) }
}
role Partial2of3[&f, $a1, $a2, ::T3, ::R] {
    multi method _(T3 $a3                        )            { apply_comp(&f($a1, $a2, $a3))           }
    multi method _(T3 $a3, *@bs                  ) is default { apply_more(&f, [$a1, $a2, $a3], @bs)    }
    multi method _(|as                           )            { die X::Typing::ArgBinding.new(self, as) }
    
    multi method postcircumfix:<( )>($as) {  enter(self, $as)                     }

    method arity { 1 }
    method count { 1 }
    method sig   { @(T3, R) }
    method ty    { typeStr(self.sig) }
}

# arity 4
role Partial0of4[&f, ::T1, ::T2, ::T3, ::T4, ::R] {
    multi method _(T1 $a1) {                                    apply_part(&f, $a1)                     }
    multi method _(T1 $a1, T2 $a2) {                            apply_part(&f, $a1, $a2)                }
    multi method _(T1 $a1, T2 $a2, T3 $a3) {                    apply_part(&f, $a1, $a2, $a3)           }
    multi method _(T1 $a1, T2 $a2, T3 $a3, T4 $a4) {            apply_comp(&f($a1, $a2, $a3, $a4))      }
    multi method _(T1 $a1, T2 $a2, T3 $a3, T4 $a4, *@bs) is default {   apply_more(&f, [$a1, $a2, $a3, $a4], @bs)    }
    multi method _(|as) {                                       die X::Typing::ArgBinding.new(self, as) }
    
    multi method postcircumfix:<( )>($as) {  enter(self, $as)                     }

    method arity { 4 }
    method count { 4 }
    method sig   { @(T1, T2, T3, T4, R) }
    method ty    { typeStr(self.sig) }
}
role Partial1of4[&f, $a1, ::T2, ::T3, ::T4, ::R] {
    multi method _(T2 $a2) {                                    apply_part(&f, $a1, $a2)                }
    multi method _(T2 $a2, T3 $a3) {                            apply_part(&f, $a1, $a2, $a3)           }
    multi method _(T2 $a2, T3 $a3, T4 $a4) {                    apply_comp(&f($a1, $a2, $a3, $a4))      }
    multi method _(T2 $a2, T3 $a3, T4 $a4, *@bs) is default {   apply_more(&f, [$a1, $a2, $a3, $a4], @bs)   }
    multi method _(|as) {                                       die X::Typing::ArgBinding.new(self, as) }
    
    multi method postcircumfix:<( )>($as) {  enter(self, $as)                     }

    method arity { 3 }
    method count { 3 }
    method sig   { @(T2, T3, T4, R) }
    method ty    { typeStr(self.sig) }
}
role Partial2of4[&f, $a1, $a2, ::T3, ::T4, ::R] {
    multi method _(T3 $a3) {                                    apply_part(&f, $a1, $a2, $a3)           }
    multi method _(T3 $a3, T4 $a4) {                            apply_comp(&f($a1, $a2, $a3, $a4))      }
    multi method _(T3 $a3, T4 $a4, *@bs) is default {           apply_more(&f, [$a1, $a2, $a3, $a4], @bs)    }
    multi method _(|as) {                                       die X::Typing::ArgBinding.new(self, as) }
    
    multi method postcircumfix:<( )>($as) {  enter(self, $as)                     }

    method arity { 2 }
    method count { 2 }
    method sig   { @(T3, T4, R) }
    method ty    { typeStr(self.sig) }
}
role Partial3of4[&f, $a1, $a2, $a3, ::T4, ::R] {
    multi method _(T4 $a4) {                                    apply_comp(&f($a1, $a2, $a3, $a4))      }
    multi method _(T4 $a4, *@bs) is default {                   apply_more(&f, [$a1, $a2, $a3, $a4], @bs)    }
    multi method _(|as) {                                       die X::Typing::ArgBinding.new(self, as) }
    
    multi method postcircumfix:<( )>($as) {  enter(self, $as)                     }

    method arity { 1 }
    method count { 1 }
    method sig   { @(T4, R) }
    method ty    { typeStr(self.sig) }
}

# arity 5
role Partial0of5[&f, ::T1, ::T2, ::T3, ::T4, ::T5, ::R] {
    multi method _(T1 $a1) {                                    apply_part(&f, $a1)                     }
    multi method _(T1 $a1, T2 $a2) {                            apply_part(&f, $a1, $a2)                }
    multi method _(T1 $a1, T2 $a2, T3 $a3) {                    apply_part(&f, $a1, $a2, $a3)           }
    multi method _(T1 $a1, T2 $a2, T3 $a3, T4 $a4) {            apply_part(&f, $a1, $a2, $a3, $a4)      }
    multi method _(T1 $a1, T2 $a2, T3 $a3, T4 $a4, T5 $a5) {    apply_comp(&f($a1, $a2, $a3, $a4, $a5)) }
    multi method _(T1 $a1, T2 $a2, T3 $a3, T4 $a4, T5 $a5, *@bs) is default {   apply_more(&f, [$a1, $a2, $a3, $a4, $a5], @bs)    }
    multi method _(|as) {                                       die X::Typing::ArgBinding.new(self, as) }
    
    multi method postcircumfix:<( )>($as) {  enter(self, $as)                     }

    method arity { 5 }
    method count { 5 }
    method sig   { @(T1, T2, T3, T4, T5, R) }
    method ty    { typeStr(self.sig) }
}
role Partial1of5[&f, $a1, ::T2, ::T3, ::T4, ::T5, ::R] {
    multi method _(T2 $a2) {                                    apply_part(&f, $a1, $a2)                }
    multi method _(T2 $a2, T3 $a3) {                            apply_part(&f, $a1, $a2, $a3)           }
    multi method _(T2 $a2, T3 $a3, T4 $a4) {                    apply_part(&f, $a1, $a2, $a3, $a4)      }
    multi method _(T2 $a2, T3 $a3, T4 $a4, T5 $a5) {            apply_comp(&f($a1, $a2, $a3, $a4, $a5)) }
    multi method _(T2 $a2, T3 $a3, T4 $a4, T5 $a5, *@bs) is default {   apply_more(&f, [$a1, $a2, $a3, $a4, $a5], @bs)   }
    multi method _(|as) {                                       die X::Typing::ArgBinding.new(self, as) }
    
    multi method postcircumfix:<( )>($as) {  enter(self, $as)                     }

    method arity { 4 }
    method count { 4 }
    method sig   { @(T2, T3, T4, T5, R) }
    method ty    { typeStr(self.sig) }
}
role Partial2of5[&f, $a1, $a2, ::T3, ::T4, ::T5, ::R] {
    multi method _(T3 $a3) {                                    apply_part(&f, $a1, $a2, $a3)           }
    multi method _(T3 $a3, T4 $a4) {                            apply_part(&f, $a1, $a2, $a3, $a4)      }
    multi method _(T3 $a3, T4 $a4, T5 $a5) {                    apply_comp(&f($a1, $a2, $a3, $a4, $a5)) }
    multi method _(T3 $a3, T4 $a4, T5 $a5, *@bs) is default {   apply_more(&f, [$a1, $a2, $a3, $a4, $a5], @bs)    }
    multi method _(|as) {                                       die X::Typing::ArgBinding.new(self, as) }
    
    multi method postcircumfix:<( )>($as) {  enter(self, $as)                     }

    method arity { 3 }
    method count { 3 }
    method sig   { @(T3, T4, T5, R) }
    method ty    { typeStr(self.sig) }
}
role Partial3of5[&f, $a1, $a2, $a3, ::T4, ::T5, ::R] {
    multi method _(T4 $a4) {                                    apply_part(&f, $a1, $a2, $a3, $a4)      }
    multi method _(T4 $a4, T5 $a5) {                            apply_comp(&f($a1, $a2, $a3, $a4, $a5)) }
    multi method _(T4 $a4, T5 $a5, *@bs) is default {           apply_more(&f, [$a1, $a2, $a3, $a4, $a5], @bs)    }
    multi method _(|as) {                                       die X::Typing::ArgBinding.new(self, as) }
    
    multi method postcircumfix:<( )>($as) {  enter(self, $as)                     }

    method arity { 2 }
    method count { 2 }
    method sig   { @(T4, T5, R) }
    method ty    { typeStr(self.sig) }
}
role Partial4of5[&f, $a1, $a2, $a3, $a4, ::T5, ::R] {
    multi method _(T5 $a5) {                                    apply_comp(&f($a1, $a2, $a3, $a4, $a5)) }
    multi method _(T5 $a5, *@bs) is default {                   apply_more(&f, [$a1, $a2, $a3, $a4, $a5], @bs)    }
    multi method _(|as) {                                       die X::Typing::ArgBinding.new(self, as) }
    
    multi method postcircumfix:<( )>($as) {  enter(self, $as)                     }

    method arity { 1 }
    method count { 1 }
    method sig   { @(T5, R) }
    method ty    { typeStr(self.sig) }
}



my sub _curry(&original, &clone, :@partialArgs) {
    my $sig = &original.signature;
    my $arity = $sig.arity;
    my $argCount = @partialArgs.elems;
    my $r = $sig.returns;
    my ($t1, $t2, $t3, $t4, $t5) = $sig.params.map(*.type);
    my ($a1, $a2, $a3, $a4, $a5) = @partialArgs;
    my $result = do given $argCount {
        when 0 {
            given $arity {
                when 1 { &original does Partial0of1[&clone, $t1                    , $r ] }
                when 2 { &original does Partial0of2[&clone, $t1, $t2               , $r ] }
                when 3 { &original does Partial0of3[&clone, $t1, $t2, $t3          , $r ] }
                when 4 { &original does Partial0of4[&clone, $t1, $t2, $t3, $t4     , $r ] }
                when 5 { &original does Partial0of5[&clone, $t1, $t2, $t3, $t4, $t5, $r ] }
            }
        }
        when 1 {
            given $arity {
                when 2 { &original does Partial1of2[&clone, $a1, $t2               , $r ] }
                when 3 { &original does Partial1of3[&clone, $a1, $t2, $t3          , $r ] }
                when 4 { &original does Partial1of4[&clone, $a1, $t2, $t3, $t4     , $r ] }
                when 5 { &original does Partial1of5[&clone, $a1, $t2, $t3, $t4, $t5, $r ] }
            }
        }
        when 2 {
            given $arity {
                when 3 { &original does Partial2of3[&clone, $a1, $a2, $t3          , $r ] }
                when 4 { &original does Partial2of4[&clone, $a1, $a2, $t3, $t4     , $r ] }
                when 5 { &original does Partial2of5[&clone, $a1, $a2, $t3, $t4, $t5, $r ] }
            }
        }
        when 3 {
            given $arity {
                when 4 { &original does Partial3of4[&clone, $a1, $a2, $a3, $t4     , $r ] }
                when 5 { &original does Partial3of5[&clone, $a1, $a2, $a3, $t4, $t5, $r ] }
            }
        }
        when 4 {
            given $arity {
                when 5 { &original does Partial4of5[&clone, $a1, $a2, $a3, $a4, $t5, $r ] }
            }
        }
    }
    
    # should not happen (I guess...)
    die "mismatch of arity $arity and nr of args $argCount"
        unless $result.defined;

    return $result;
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
        if (&f ~~ Partial0of1)
        || (&f ~~ Partial0of2) || (&f ~~ Partial1of2)
        || (&f ~~ Partial0of3) || (&f ~~ Partial1of3) || (&f ~~ Partial2of3)
        || (&f ~~ Partial0of4) || (&f ~~ Partial1of4) || (&f ~~ Partial2of4) || (&f ~~ Partial3of4)
        || (&f ~~ Partial0of5) || (&f ~~ Partial1of5) || (&f ~~ Partial2of5) || (&f ~~ Partial3of5) || (&f ~~ Partial4of5)
    ;

    my @ps = &f.signature.params;
    my $arity = @ps.elems;
    die "cannot curry nullary fn - signature: {&f.signature.perl}; fn: {&f.gist}" 
        if $arity == 0;
    die "cannot curry fn with optional/slurpy/named/capture or parcel parameters - signature: {&f.signature.perl}; fn: {&f.gist}"
        if @ps.map({$_.optional || $_.slurpy || $_.named || $_.capture || $_.parcel}).any;
    die "NYI: Fn with arity $arity (> 5) - signature: {&f.signature.perl}; fn: {&f.gist}"
        if $arity > 5;

    return _curry(&f, &f.clone);
}
