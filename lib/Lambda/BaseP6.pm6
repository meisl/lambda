use v6;
use Lambda::P6Currying;

module Lambda::BaseP6;


role lambda is export {
    has Str $.lambda;

    has &!makeLambda;

    method lambda is default {
        $!lambda //= &!makeLambda();
    }

    submethod BUILD(:$lambda) {  # MUST be named arg - and named exactly like this!! Doesn't work with positional arg, neither with multi submethod BUILD
        if ($lambda.defined) {
            if $lambda ~~ Str {
                $!lambda = $lambda;
                return self;
            } elsif $lambda ~~ Callable {
                die "thunk must not expect any args, got  " ~ $lambda.perl
                    unless $lambda.arity == 0;
                #warn "got code: {$lambda.perl}";
                &!makeLambda = $lambda;
                return self;
            }
        }
        die "need a Str:D or a Callable:D, got " ~ $lambda.perl;
    }

    method Str {
        self.?symbol // self.lambda;
    }
    method gist { self.Str }
}

role Definition is export {
    has Str $.symbol;

    submethod BUILD(Str:D :$symbol) {
        $!symbol = $symbol;
    }

    method Str { $!symbol }
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
        $out does lambda(:lambda($lx));
        $out does Definition(:$symbol)
            if $symbol.defined;
        $out = curry($out);
        $out;
    }
}

