use v6;

use Lambda::Base;
use Lambda::BaseP6;
use Lambda::Boolean;
use Lambda::String;
use Lambda::PairADT;
use Lambda::MaybeADT;
use Lambda::ListADT;


module Lambda::Parser;
# Parser a: Str -> (Maybe (Pair a Str))


# basic parsers nxt_P and fail_P & generator return_P -------------------------

# return_P: a -> Parser a
constant $return_P is export = lambdaFn(
    'return_P', 'λx.λs.Some (Pair x s)',
    -> $x {
        lambdaFn(Str, { my $xStr = $x.?name // $x.?lambda // $x.perl; "(return_P $xStr)" },
            -> Str:D $s { $Some($Pair($x, $s)) }
        )
    }
);

# fail_P: Parser a
constant $fail_P is export = lambdaFn(
    'fail_P', 'λs.None',
    -> Str:D $s { $None }
);

# nxt_P: Parser Str
constant $nxt_P is export = lambdaFn(
    'nxt_P', 'λs.case-Str s (ε (fail_P s)) return_P',
    -> Str:D $s {
        case-Str($s,
            ε =>  { $fail_P($s) },
            $return_P
        )
    }
);


# parser combinators seq_P (aka bind_Parser) + alt_P (aka choice_P) -----------

# seq_P (aka bind_Parser): Parser a -> (a -> Parser b) -> Parser b
constant $seq_P is export = lambdaFn(   # this is bind for the Parser Monad
    'seq_P', 'λp.λf.λs.case (p s) (None (fail_P s)) (Some <x, out> (f x out))',
    -> $p, $f {
        lambdaFn(Str, { my $fStr = $f.?name // $f.?lambda // $f.perl; "$p >>= $fStr" },
            -> Str:D $s {
                case-Maybe($p($s),
                    None => { $fail_P($s) },
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

# simple parser (generator)s sat_P, char_P, string_P --------------------------

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
    'chr_P', 'λc.sat_P (Str-eq? c)',    # = `sat_P ° Str-eq?`
    -> Str:D $c { $sat_P($Str-eq($c)) }
);


# parser combinators oneOrZero ("?"), many ("*") and many1 ("+") --------------

# oneOrZero_P: Parser a -> Parser [a]
constant $oneOrZero_P is export = lambdaFn(
    'oneOrZero_P', 'λp.(nxt_P >>= λc.return_P (cons c nil)) +++ (return_P nil)',
    -> $p {
        $alt_P(
            $seq_P($p, -> $c {
                          $return_P($cons($c, $nil))
            }),
            $return_P($nil)
        )
    }
);

# many_P-foldl: (b -> a -> b) -> b -> Parser a -> Parser b
constant $many_P-foldl is export = $Y(-> &self { lambdaFn(
    'many_P-foldl', 'Y λself.λf.λstart.λp.(p >>= λv.self f (f start v) p) +++ (return_P start)',
    -> $f, $start {
        -> $p {
            $alt_P(
                $seq_P($p, -> $v {
                              &self($f, $f($start, $v), $p)
                }),
                $return_P($start)
            );
        }
    }
)});

# many_P-foldr: (a -> b -> b) -> b -> Parser a -> Parser b
constant $many_P-foldr is export = $Y(-> &self { lambdaFn(
    'many_P-foldr', 'Y λself.λf.λstart.λp.(p >>= λv.(self f start p) >>= λacc.return_P (f v acc)) +++ (return_P start)',
    -> $f, $start {
        -> $p {
            $alt_P(
                $seq_P($p,                      -> $v { 
                $seq_P(&self($f, $start, $p),   -> $acc {
                                                   $return_P($f($v, $acc))
                })}),
                $return_P($start)
            );
        }
    }
)});


# many1_P-foldl: (b -> a -> b) -> b -> Parser a -> Parser b
constant $many1_P-foldl is export = lambdaFn(
    'many1_P-foldl', 'λf.λstart.λp.p >>= λv.(many_P-foldl f (f start v) p)',
    -> $f, $start {
        -> $p {
            $seq_P($p, -> $v {
                          $many_P-foldl($f, $f($start, $v), $p)
            })
        }
    }
);

# many1_P-foldr: (a -> b -> b) -> b -> Parser a -> Parser b
constant $many1_P-foldr is export = lambdaFn(
    'many1_P-foldr', 'λf.λstart.λp.p >>= λv.(many_P-foldr f start p) >>= λacc.return_P (f v acc)',
    -> $f, $start {
        -> $p {
            $seq_P($p,                            -> $v {
            $seq_P($many_P-foldr($f, $start, $p), -> $acc {
                                                     $return_P($f($v, $acc))
            })})
        }
    }
);


# many1_P-foldl1: (a -> a -> a) -> Parser a -> Parser a
constant $many1_P-foldl1 is export = lambdaFn(
    'many1_P-foldl1', 'λf.λp.p >>= λv.many_P-foldl f v p',
    -> $f {
        -> $p {
            $seq_P($p, -> $v {
                          $many_P-foldl($f, $v, $p)
            })
        }
    }
);

# many1_P-foldr1: (a -> a -> a) -> a -> Parser a -> Parser a
constant $many1_P-foldr1 is export = lambdaFn(
    'many1_P-foldr1', 'λf.λp.NYI',
    -> $f {
        -> $p { # TODO: think about a more efficient impl, which avoid the intermediary list
            $seq_P($many1_P-foldr($cons, $nil, $p), -> TList $vs {
                                                       $return_P($foldr1($f, $vs))
            })
        }
    }
);



constant $many_P is export = lambdaFn(
    'many_P', 'many_P-foldr cons nil',
    $many_P-foldr($cons, $nil)
);

constant $many1_P is export = lambdaFn(
    'many1_P', 'many1_P-foldr cons nil',
    $many1_P-foldr($cons, $nil)
);



constant $str_P_ZZZ is export = $Y(-> &self { lambdaFn(
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

# str_P: Str -> Parser Str
# abstracts from low-level case-Str
constant $str_P is export = lambdaFn(
    'str_P', 'fst ° Some->value ° (many_P-foldl (λacc.λc.acc >>= λs.(chr_P c) >>= λ_.return_P (s ~ c)) (return_P "") nxt_P)',
    $B($fst, $B($Some2value, $many_P-foldl(
        -> $acc, $c { 
            $seq_P($acc,       -> $s {
            $seq_P($chr_P($c), -> Mu {
                                  $return_P($Str-concat($s, $c))
            })} does lambda("λs.(chr_P {$c.perl}) >>= λ_.return_P (s ~ {$c.perl})"))
        },
        $return_P(""),
        $nxt_P
    )))
);

# character class parser (generator)s anyOf_P and noneOf_P --------------------

# anyOf_P: Str -> Parser Chr
constant $anyOf_P is export = lambdaFn(
    'anyOf_P', 'λs.sat_P (foldl1 (λleft.λright.λc.if (left c) #true (right c)) (map Str-eq? (fst (Some->value (many1_P nxt_P s)))))',
    -> Str:D $s {
        case-Maybe($many1_P($nxt_P)($s),
            None => { die "empty character class" },
            Some => -> $out {
                $out(-> $cs, Mu {   # TODO: pattern-match a Pair
                    $sat_P($foldl1(
                        -> $left, $right { 
                            -> $c {
                                _if_($left($c), # short-circuit OR
                                    $true,
                                    { $right($c) }
                                )
                            } 
                        }, 
                        $map($Str-eq, $cs)
                    ))
                })
            }
        )
    }
);


# noneOf_P: Str -> Parser Chr
constant $noneOf_P is export = lambdaFn(
    'noneOf_P', 'λs.sat_P (foldl1 (λleft.λright.λc.if (left c) (right c) #false) (map Str-ne? (fst (Some->value (many1_P nxt_P s)))))',
    -> Str:D $s {
        case-Maybe($many1_P($nxt_P)($s),
            None => { die "empty character class" },
            Some => -> $out {
                $out(-> $cs, Mu {   # TODO: pattern-match a Pair
                    $sat_P($foldl1(
                        -> $left, $right { 
                            -> $c {
                                _if_($left($c), # short-circuit AND
                                    { $right($c) },
                                    $false
                                )
                            } 
                        }, 
                        $map($Str-ne, $cs)
                    ))
                })
            }
        )
    }
);


# linebreak, whitespace, etc --------------------------------------------------

# linebreak_P: Parser Str
constant $linebreak_P is export = lambdaFn(
    'linebreak_P', '(sat_P CR? >>= λ_.sat_P LF? >>= λ_.return_P "\r\n") +++ (sat_P (or LF? CR?))',
    $alt_P(
        $seq_P($sat_P($is-CR), -> Mu { $seq_P($sat_P($is-LF), -> Mu { $return_P("\r\n") }) }),
        $sat_P(-> $c {
            _if_($is-LF($c),    # short-circuit OR
                $true,
                { $is-CR($c) }
            )
        })
    )
);

