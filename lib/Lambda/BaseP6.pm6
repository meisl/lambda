use v6;
use Lambda::P6Currying;



module Lambda::BaseP6;


role Definition is export {
    has Str $.name;

    method symbol { $!name }
    method Str  { $!name }
    method gist { $!name }
}


my sub insistOnArityZeroThunk(Code:D $thunk) {
    die "thunk must not expect any args, got  " ~ $thunk.perl
        unless $thunk.arity == 0;
    return $thunk;
}

role lambda is export {
    has        $.init;
    has Str:D  $!lambda;
    has        &!makeLambda;

    method lambda {
        $!lambda //= &!makeLambda();
    }

    # roles with initialization value 
    # - must have exactly one public attribute
    # - are initialized by calling BUILD with one named arg, where the name of the arg is exactly the attribute's name
    #   (compiler inserts this invocation at the call site, ie. where you say `does Foo(...)`)
    # So, in order to pass multiple initialization values we can use a single (named) *parcel* parameter:
    #
    # Also note: strangely, we cannot use multi submethod BUILD, subsequently mixed-in roles will confuse which BUILD to call...(?!)

    submethod BUILD(|args) {
        return self._BUILD(|args);
    }

    multi method _BUILD(:$!init! is parcel (Str:D $lambda, Str $name?)) {
        $!lambda = $lambda;
        return self;
    }

    multi method _BUILD(:$!init! is parcel (Code:D $lambda, Str $name?)) {
        #warn "got code: {$lambda.perl}";
        &!makeLambda = insistOnArityZeroThunk $lambda;
        return self;
    }

    multi method _BUILD(Str:D :$init!) {
        $!lambda = $init;
        $!init = $($!lambda, Str);
        return self;
    }

    multi method _BUILD(Code:D :$init!) {
        &!makeLambda = insistOnArityZeroThunk $init;
        $!init = $(Str, Str);
        return self;
    }


    method symbol { $!init[1] } # TODO: remove method `symbol` from role lambda
    method name { $!init[1] }
    method Str  { $!init[1] // self.lambda }
    method gist { self.Str }
}


sub lambdaFn(Str $symbol, $lambdaExpr, &f) is export {
    my $arity = &f.?arity // &f.signature.params.elems;
    if $arity == 0 {
        die "cannot make lambda function with zero parameters: symbol=$symbol, lambdaExpr=$lambdaExpr, &f.signature=" ~ &f.signature.perl ~ ', &f=' ~ &f.perl;
    } else {
        my $out = &f;
        my $lx;
        if ($lambdaExpr ~~ Str) && ($lambdaExpr.defined) {
            $lx = $lambdaExpr.substr(0, 1) eq '(' ?? $lambdaExpr !! "($lambdaExpr)";
            #warn ">>>>> $lambdaExpr -> $lx";
        } else {
            $lx = { my $out = $lambdaExpr(); $out.substr(0, 1) eq '(' ?? $out !! "($out)" };
        }
        
        $out does lambda(($lx, $symbol));
        $out = curry($out);
        $out;
    }
}

#`{
    multi sub trait_mod:<is>(Routine:D $f, Str:D :$LAMBDA!) is export {
        lambdaFn(Str, $LAMBDA, $f);
    }

    my $f = -> Str $x, Int $y { $x x $y };
    my $fl = lambdaFn('foo', 'λx.x', $f);
    say $fl;
}


