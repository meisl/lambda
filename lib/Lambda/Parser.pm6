use v6;

use Lambda::Base;
use Lambda::BaseP6;
use Lambda::Boolean;
use Lambda::String;
use Lambda::PairADT;
use Lambda::MaybeADT;
use Lambda::ListADT;

module Lambda::Parser;
# Parser a: Str -> (List (Pair a Str))


# basic parsers ---------------------------------------------------------------

constant $return_P is export = lambdaFn(
    'return_P', 'λx.λs.Some (Pair x s)',
    -> $x, Str:D $s { $Some($Pair($x, $s)) }
);

constant $fail_P is export = lambdaFn(
    'fail_P', 'λs.None',
    -> Str:D $s { $None }
);

# nxt_P: Parser Str
constant $nxt_P is export = lambdaFn(
    'nxt_P', 'λs.case-Str s (ε (fail_P s)) return_P',
    -> Str:D $s {
        case-Str($s,
            ε => $None, # = fail_P($s)
            $return_P
        )
    }
);


# parser combinators seq_P (aka bind_Parser) + alt_P (aka choice_P) -----------

# seq_P (aka bind_Parser): Parser a -> (a -> Parser b) -> Parser b
constant $seq_P is export = lambdaFn(   # this is bind for the Parser Monad
    'seq_P', 'λp.λf.λs.case (p s) (None (fail_P s)) (Some <x, out> (f x out))',
    -> $p, $f {
        lambdaFn(Str, '',
            -> Str:D $s {
                case-Maybe($p($s),
                    None => $None,  # = $fail_P($s)
                    #Some => -> TPair $result { $result($f) }    # = $f($fst($result), $snd($result)), requires $f to be curried
                    Some => -> TPair $result { $result(-> $a, $b { $f($a)($b) }) }    # = $f($fst($result), $snd($result))
                )
            }
        )
    }
);

# alt_P (aka choice_Parser): Parser a -> Parser a -> Parser a
constant $alt_P is export = lambdaFn(
    'alt_P', 'λp.λq.λs.(λpOut.case pOut (None (q s)) (Some _ pOut)) (p s)',
    -> $p, $q {
        lambdaFn(Str, '',
            -> Str:D $s {
                my $pResult = $p($s);
                case-Maybe($pResult,
                    None => $q($s),
                    Some => -> Mu { $pResult }
                )
            }
        )
    }
);


# simple parsers sat_P, char_P, string_P --------------------------------------

# sat_P: (Str -> Bool) -> Parser Str
constant $sat_P is export = lambdaFn(
    'sat_P', 'λpred.λs.nxt_P >>= λc.if (pred c) (return_P c) fail_P ',
    -> $pred {
        $seq_P($nxt_P, -> Str:D $c {
            _if_($pred($c),
                { $return_P($c) },
                $fail_P
            )
        })
    }
);

constant $chr_P is export = lambdaFn(
    'chr_P', 'λc.sat_P (Str-eq? c)',
    -> Str:D $c { $sat_P(-> $d { $Str-eq($c, $d) }) }
);

constant $str_P is export = $Y(-> &self { lambdaFn(
    'str_P', 'Y λself.λs.(λreturn-s.case s (ε return-s) (λc.λcs.(self c) >>= λ_.(self cs) >>= λ_.return-s)) (return_P s)',
    -> Str:D $s {
        my $return-s = $return_P($s);
        case-Str($s,
            ε => $return-s,
            -> $c, $cs {
                $seq_P($chr_P($c),  -> Mu {
                $seq_P(&self($cs),  -> Mu {
                     $return-s
                })})
            }
        )
    }
)});


# parser combinators many + many1 ---------------------------------------------

constant $many_P is export = $Y(-> &self { lambdaFn(
    'many_P', 'Y λself.λp.λs.case (p s) (None (return_P nil s)) (Some <v, rest> ((self p >>= λvs.return_P v vs) rest))',
    -> $p {
        lambdaFn(Str, '',
            -> Str:D $s {
                case-Maybe($p($s),
                    None => { $return_P($nil, $s) },
                    Some => -> TPair $out {
                        $out(-> $v, Str:D $rest {   # TODO: pattern-match a Pair
                            $seq_P(&self($p),   -> TList $vs {
                                $return_P($cons($v, $vs))
                            }).($rest)
                        })
                    }
                )
            }
        )
    }
)});

constant $many1_P is export = lambdaFn(
    'many1_P', 'λp.p >>= λv.(many_P p) >>= λvs.return_P (cons v vs)',
    -> $p {
        $seq_P($p,          -> $v {
        $seq_P($many_P($p), -> $vs {
            $return_P($cons($v, $vs))
        })})
    }
);

