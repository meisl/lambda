use v6;


my $nApp_c = 0; # "complete" application
my $nApp_o = 0; # "over-" application
my $nApp_p = 0; # "partial" application

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

my sub dieUnapplicable($self, Capture:D $args) {
    die X::Typing::Unapplicable.new(:whatsInFuncPos($self), :$args);
}

my role Unapplicable {
    multi method invoke(*@pos, *%nmd) {
        dieUnapplicable(self, \(@pos, %nmd));
    }
    multi method invoke(Capture:D $args) {  # TODO: remove once Rakudo* 2015-02 has landed
        dieUnapplicable(self, $args);
    }
    method _(|args) {    # "over-applying" will come here
        dieUnapplicable(self, args);
    }
}

my sub typeStr(@types) {
    @types.map(*.perl).join(' -> ');
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

# Dispatch to one of the _ methods, with positional args unpacked, or die if there are named args
# NOTE: doesn't work with postcircumfix:<( )> overrides there, for some reason...?!
# TODO: remove once Rakudo* 2015-02 has landed (when invoke/postcircumfix:<( )> will get args *as is*, rather than a Capture)
my sub enter($self, @pos, %nmd) {
    die X::Typing::UnsupportedNamedArgs.new(:whatsInFuncPos($self), :args(\(@pos, %nmd)))
        unless %nmd.elems == 0;
    $self._(|@pos);
}

# gets called if none of the _ signatures matches (~> invalid call)
my sub dieArgBinding($self, Capture:D $args) {
    die X::Typing::ArgBinding.new($self, $args)
}

# arity 1
role C1[&f, ::T1, ::R] {
    multi method _(T1 $a1                               )            { $nApp_c++; apply_comp(&f($a1))                                       }
    multi method _(T1 $a1, *@bs                         ) is default { $nApp_o++; apply_comp(&f($a1))._(|@bs)                               }
    multi method _(|as                                  )            { dieArgBinding(self, as)                                              }

    multi method invoke(*@pos, *%nmd) { enter(self, @pos, %nmd) }
    multi method invoke(Capture:D $as) { enter(self, $as.list, $as.hash) }  # TODO: remove once Rakudo* 2015-02 has landed

    method arity { 1 }
    method count { 1 }
    method sig   { @(T1, R) }
    method ty    { typeStr(self.sig) }
}

# arity 2
role C2[&f, ::T1, ::T2, ::R] {
    multi method _(T1 $a1                               )            { $nApp_p++; {...} does C1[{ &f($a1, $^b) }, T2, R]                    }
    multi method _(T1 $a1, T2 $a2                       )            { $nApp_c++; apply_comp(&f($a1, $a2))                                  }
    multi method _(T1 $a1, T2 $a2, *@bs                 ) is default { $nApp_o++; apply_comp(&f($a1, $a2))._(|@bs)                          }
    multi method _(|as                                  )            { dieArgBinding(self, as)                                              }

    multi method invoke(*@pos, *%nmd ) { enter(self, @pos, %nmd) }
    multi method invoke(Capture:D $as) { enter(self, $as.list, $as.hash) }  # TODO: remove once Rakudo* 2015-02 has landed

    method arity { 2 }
    method count { 2 }
    method sig   { @(T1, T2, R) }
    method ty    { typeStr(self.sig) }
}

# arity 3
role C3[&f, ::T1, ::T2, ::T3, ::R] {
    multi method _(T1 $a1                               )            { $nApp_p++; {...} does C2[{ &f($a1, $^b, $^c) }, T2, T3, R]           }
    multi method _(T1 $a1, T2 $a2                       )            { $nApp_p++; {...} does C1[{ &f($a1, $a2, $^c) },     T3, R]           }
    multi method _(T1 $a1, T2 $a2, T3 $a3               )            { $nApp_c++; apply_comp(&f($a1, $a2, $a3))                             }
    multi method _(T1 $a1, T2 $a2, T3 $a3, *@bs         ) is default { $nApp_o++; apply_comp(&f($a1, $a2, $a3))._(|@bs)                     }
    multi method _(|as                                  )            { dieArgBinding(self, as)                                              }

    multi method invoke(*@pos, *%nmd ) { enter(self, @pos, %nmd) }
    multi method invoke(Capture:D $as) { enter(self, $as.list, $as.hash) }  # TODO: remove once Rakudo* 2015-02 has landed

    method arity { 3 }
    method count { 3 }
    method sig   { @(T1, T2, T3, R) }
    method ty    { typeStr(self.sig) }
}

# arity 4
role C4[&f, ::T1, ::T2, ::T3, ::T4, ::R] {
    multi method _(T1 $a1                               )            { $nApp_p++; {...} does C3[{ &f($a1, $^b, $^c, $^d) }, T2, T3, T4, R]  }
    multi method _(T1 $a1, T2 $a2                       )            { $nApp_p++; {...} does C2[{ &f($a1, $a2, $^c, $^d) },     T3, T4, R]  }
    multi method _(T1 $a1, T2 $a2, T3 $a3               )            { $nApp_p++; {...} does C1[{ &f($a1, $a2, $a3, $^d) },         T4, R]  }
    multi method _(T1 $a1, T2 $a2, T3 $a3, T4 $a4       )            { $nApp_c++; apply_comp(&f($a1, $a2, $a3, $a4))                        }
    multi method _(T1 $a1, T2 $a2, T3 $a3, T4 $a4, *@bs ) is default { $nApp_o++; apply_comp(&f($a1, $a2, $a3, $a4))._(|@bs)                }
    multi method _(|as                                  )            { dieArgBinding(self, as)                                              }

    multi method invoke(*@pos, *%nmd ) { enter(self, @pos, %nmd) }
    multi method invoke(Capture:D $as) { enter(self, $as.list, $as.hash) }  # TODO: remove once Rakudo* 2015-02 has landed

    method arity { 4 }
    method count { 4 }
    method sig   { @(T1, T2, T3, T4, R) }
    method ty    { typeStr(self.sig) }
}

# arity 5
role C5[&f, ::T1, ::T2, ::T3, ::T4, ::T5, ::R] {
    multi method _(T1 $a1                                      )            { $nApp_p++; {...} does C4[{ &f($a1, $^b, $^c, $^d, $^e) }, T2, T3, T4, T5, R]  }
    multi method _(T1 $a1, T2 $a2                              )            { $nApp_p++; {...} does C3[{ &f($a1, $a2, $^c, $^d, $^e) },     T3, T4, T5, R]  }
    multi method _(T1 $a1, T2 $a2, T3 $a3                      )            { $nApp_p++; {...} does C2[{ &f($a1, $a2, $a3, $^d, $^e) },         T4, T5, R]  }
    multi method _(T1 $a1, T2 $a2, T3 $a3, T4 $a4              )            { $nApp_p++; {...} does C1[{ &f($a1, $a2, $a3, $a4, $^e) },             T5, R]  }
    multi method _(T1 $a1, T2 $a2, T3 $a3, T4 $a4, T5 $a5      )            { $nApp_c++; apply_comp(&f($a1, $a2, $a3, $a4, $a5))                            }
    multi method _(T1 $a1, T2 $a2, T3 $a3, T4 $a4, T5 $a5, *@bs) is default { $nApp_o++; apply_comp(&f($a1, $a2, $a3, $a4, $a5))._(@bs)                     }
    multi method _(|as                                  )                   { dieArgBinding(self, as)                                                       }

    multi method invoke(*@pos, *%nmd ) { enter(self, @pos, %nmd) }
    multi method invoke(Capture:D $as) { enter(self, $as.list, $as.hash) }  # TODO: remove once Rakudo* 2015-02 has landed

    method arity { 5 }
    method count { 5 }
    method sig   { @(T1, T2, T3, T4, T5, R) }
    method ty    { typeStr(self.sig) }
}



my sub _curry(&original, &clone -->Callable) {
    my $sig = &original.signature;
    my $arity = $sig.arity;
    my $r = $sig.returns;
    my ($t1, $t2, $t3, $t4, $t5) = $sig.params.map(*.type);
    given $arity {
        when 1 { &original does C1[&clone, $t1                    , $r ] }
        when 2 { &original does C2[&clone, $t1, $t2               , $r ] }
        when 3 { &original does C3[&clone, $t1, $t2, $t3          , $r ] }
        when 4 { &original does C4[&clone, $t1, $t2, $t3, $t4     , $r ] }
        when 5 { &original does C5[&clone, $t1, $t2, $t3, $t4, $t5, $r ] }
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

    return _curry(&f, &f.clone);
}

