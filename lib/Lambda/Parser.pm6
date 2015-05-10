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
# always succeeds with the given value, leaving the remainder string untouched
constant $return_P is export = lambdaFn(
    'return_P', 'λx.λs.Some (Pair x s)',
    -> $x {
        lambdaFn(Str, { my $xStr = $x.?name // $x.?lambda // $x.perl; "return_P $xStr" },
            -> Str:D $s { $Some($Pair($x, $s)) }
        )
    }
);

# fail_P: Parser a
# always fails leaving the remainder string untouched
constant $fail_P is export = lambdaFn(
    'fail_P', 'λs.None',
    -> Str:D $s { $None }
);

# nxt_P: Parser Chr
# fails on empty string or succeds with the first character removed from the beginning of remainder string
constant $nxt_P is export = lambdaFn(
    'nxt_P', 'λs.case-Str s (ε (fail_P s)) return_P',
    -> Str:D $s {
        case-Str($s,
            ε =>  { $fail_P($s) },
            $return_P
        )
    }
);


# apply a parser and die if it fails or doesn't consume the whole input
constant $parse is export = lambdaFn(
    'parse', 'λs.NYI',
    -> $p, $onFailure, Str:D $s {
        case-Maybe($p($s),
            None => {
                ($onFailure ~~ Block) && ($onFailure.arity == 0) 
                ?? $onFailure()    # simulate lazy evaluation by passing a thunk
                !! $onFailure
            },
            Some => -> TPair $result {
                $result(-> $v, $rest {  # TODO: pattern-match a Pair
                    case-Str($rest,
                        ε => $v,
                        -> Mu, Mu { die "unmatched input: {$rest.perl}" }
                    )
                })
            }
        )
    }
);

# parser combinators seq_P (aka bind_Parser) + alt_P (aka choice_P) -----------

# seq_P (aka bind_Parser): Parser a -> (a -> Parser b) -> Parser b
constant $seq_P is export = lambdaFn(   # this is bind for the Parser Monad
    'seq_P', 'λp.λf.λs.case (p s) (None (fail_P s)) (Some <x, out> (f x out))',
    -> $p, $f {
        lambdaFn(Str, {
                        my $fStr = $f.?name // ($f.^can('lambda') ?? $f.lambda.substr(1, *-1) !! $f.lambda) // $f.perl;
                        "($p >>= $fStr)";
                      },
            -> Str:D $s {
                my $pOut = $p($s);
                case-Maybe($pOut,
                    None => $pOut,
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
                my $pOut = $p($s);
                case-Maybe($pOut,
                    None => { $q($s) },
                    Some => -> Mu { $pOut }
                )
            }
        )
    }
);

# simple parser (generator)s sat_P, char_P, string_P --------------------------

# sat_P: (Chr -> Bool) -> Parser Chr
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
    -> Str:D $c { 
        $sat_P($Str-eq($c)) does lambda({ "(chr_P {$c.perl})" })
    }
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
constant $str_P_YYY is export = lambdaFn(
    'str_P', 'fst ° Some->value ° (many_P-foldl (λaccP.λc.accP >>= λs.(chr_P c) >>= λ_.return_P (s ~ c)) (return_P "") nxt_P)',
    $B($fst, $B($Some2value, $many_P-foldl(
        -> $accP, $c { 
            $seq_P($accP,      -> $s {
            $seq_P($chr_P($c), -> Mu {
                                  $return_P($Str-concat($s, $c))
            })} does lambda("λs.(chr_P {$c.perl}) >>= λ_.return_P (s ~ {$c.perl})"))
        },
        $return_P(""),
        $nxt_P
    )))
);

constant $str_P_XXX is export = lambdaFn(
    'str_P', 'fst ° Some->value ° (many_P-foldl (λacc.λcP.acc >>= λt.cP >>= λc.return_P (t ~ c)) (return_P "") (nxt_P >>= λc.return_P (chr_P c)))',
    $B($fst, $B($Some2value, $many_P-foldl(
        -> $accP, $cP { 
            $seq_P($accP,      -> $s {
            $seq_P($cP,        -> $c {
                                  $return_P($Str-concat($s, $c))
            })} does lambda("λs.$cP >>= λc.return_P (s ~ c)"))
        },
        $return_P(""),
        $seq_P($nxt_P, -> $c { $return_P($chr_P($c)) })
    )))
);

constant $str_P is export = {
    # first we make a parser for inpStr; of type Parser [Parser Chr]
    # ie. it produces a list of (chr_P c)s, one for each Chr c in inpStr
    my $inpP = $many_P($seq_P($nxt_P, -> $c { $return_P($chr_P($c)) }));
    lambdaFn(
        'str_P', 'λinpStr.NYI',
        -> Str:D $inpStr {
            # next we parse the inputStr, giving the list of (chr_P c)s)
            # my TList $chrPs = $fst($Some2value($inpP($inpStr)));
            my TList $chrPs = $parse($inpP, { die "should not happen" }, $inpStr);

            my $returnInp = $return_P($inpStr); # reads nothing and returns inpStr
            case-List($chrPs,
                nil => $returnInp,  # inpStr == ε, so the output parser is (return_P "")
                cons => -> $hd, TList $tl {
                    case-List($tl,
                        nil => $hd, # inpStr is just one character (so we don't >>= returnInp)
                        cons => -> Mu, Mu {
                            #$seq_P(    # eg: (str_P "foo") ~> ((((chr_P "f") >>= λ_.chr_P "o") >>= λ_.chr_P "o") >>= λ_.return_P "foo")
                            #    #$foldl($seq_P, $hd, $map($K, $tl)),
                            #    $foldl(-> $acc, $p { $seq_P($acc, $K($p)) }, $hd, $tl),
                            #    $K($returnInp)
                            #)
                            $foldr(    # eg: (str_P "foo") ~> ((chr_P "f") >>= λ_.(chr_P "o") >>= λ_.(chr_P "o") >>= λ_.return_P "foo")
                                -> $p, $acc { $seq_P($p, $K($acc)) },
                                $returnInp,
                                $chrPs
                            )
                        }
                    )
                }
            )
        }
    );
}();

constant $str_P_WWW is export = lambdaFn(
    'str_P', 'λinpStr.built-in',
    -> Str:D $inpStr {
        my $n = $inpStr.chars;
        given $n {
            when 0 { $return_P("") }
            when 1 { $chr_P($inpStr) }
            default {
                lambdaFn(
                    Str, "(str_P {$inpStr.perl})",
                    -> Str:D $s {
                        _if_($Str-eq($inpStr, $s.substr(0, $n)),
                            { $return_P($inpStr).($s.substr($n)) },
                            { $fail_P($s) }
                        )
                    }
                )
            }
        }
    }
);

# character class parser (generator)s anyOf_P and noneOf_P --------------------

# anyOf_P: Str -> Parser Chr
constant $anyOf_P is export = lambdaFn(
    'anyOf_P', 'λs.sat_P (foldl1 (λleft.λright.λc.if (left c) #true (right c)) (map Str-eq? (fst (Some->value (many1_P nxt_P s)))))',
    -> Str:D $s {
        #my $inpP = $many1_P-foldl1( $seq_P($nxt_P, -> $c { $return_P($Str-eq($c)) }) );
        #my TList $eqs = $parse($inpP, { die "empty character class" }, $s);
        
        
        my $inpP = $many1_P-foldl1(
            -> $left, $right { 
                -> $c {
                    _if_($left($c), # short-circuit OR
                        $true,
                        { $right($c) }
                    )
                } 
            }, 
            $seq_P($nxt_P, -> $c { $return_P($Str-eq($c)) })
        );
        $sat_P($parse($inpP, { die "empty character class" }, $s));
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

