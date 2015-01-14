use v6;

use Lambda::P6Currying;


module Lambda::BaseP6;


role lambda is export {
    has Str:D $.lambda;
    method Str {
        self.?symbol || $!lambda;
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



        #T.perl ~ ' -> ' ~ @!restParams.map(*.perl ~ ' ->') ~ ' ' ~ R.perl;

role Curried {
    method lambdaStr(*@args) {
            '(' ~ self  ~ @args.map( -> $a {' ' ~ ($a.?symbol // $a.?lambda // $a.perl) }) ~ ')'
    }

    method partial(&f, *@args) {
        lambdaFn(Str, self.lambdaStr(@args), &f);
    }
}

sub lambdaStr($self, *@args) {
        '(' ~ $self ~ @args.map( -> $a {' ' ~ ($a.?symbol // $a.?lambda // $a.perl) }) ~ ')'
}

sub lambdaFn(Str $symbol, Str:D $lambdaExpr, &f) is export {
    my $arity = &f.?arity // &f.signature.params.elems;
    if $arity == 0 {
        die "cannot make lambda function with zero parameters: symbol=$symbol, lambdaExpr=$lambdaExpr, &f.signature=" ~ &f.signature.perl ~ ', &f=' ~ &f.perl;
    } else {
        my $out = curry(&f);
        my $lx = $lambdaExpr.substr(0, 1) eq '(' ?? $lambdaExpr !! "($lambdaExpr)";
        $out does lambda($lx);
        $out does Definition(:$symbol)
            if $symbol.defined;
        $out;
    }
}
