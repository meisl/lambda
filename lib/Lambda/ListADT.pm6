use v6;

use Lambda::Base;
use Lambda::BaseP6;
use Lambda::Boolean;
use Lambda::MaybeADT;

module Lambda::ListADT;
# data List = nil
#           | cons car:_ cdr:List
role TList is export {
}


# pattern-matching ------------------------------------------------------------

multi sub case-List(TList:D $instance,
    :nil($onNil)!,
    :cons($onCons)!
) is export {
    $instance($onNil, $onCons);
}


multi sub case-List(|args) {
    die "error applying case-List: " ~ args.perl;
}


# constructors ----------------------------------------------------------------

constant $nil is export = lambdaFn(
    'nil', 'λonNil.λonCons.onNil',
    -> $onNil, $onCons {
        ($onNil ~~ Block) && ($onNil.arity == 0) 
        ?? $onNil()    # simulate lazy evaluation by passing a thunk (needed only for ctors of arity 0)
        !! $onNil
    }
) does TList;

constant $cons is export = lambdaFn(
    'cons', 'λx.λxs.λonNil.λonCons.onCons x xs',
    -> $x, TList:D $xs -->TList{
        lambdaFn(
            Str, { "(cons {$x.?symbol // $x.?lambda // $x.perl} $xs)" },
            -> $onNil, $onCons {
                $onCons($x, $xs)
            }
        ) does TList
    }
);

constant $K1nil is export = $K1($nil);
constant $K2nil is export = $K2($nil);

# predicates ----------------------------------------------------------------

constant $is-nil is export = lambdaFn(
    'nil?', 'λxs.xs #true λ_.λ_.#false',
    -> TList:D $xs { case-List($xs, nil => $true, cons => $K2false) }
);

constant $is-cons is export = lambdaFn(
    'cons?', 'λxs.xs #false λ_.λ_.#true',
    -> TList:D $xs { case-List($xs, nil => $false, cons => $K2true) }
);


# projections

my constant $cXr-nil-error = -> Str $fnName { die "cannot get $fnName of nil" };

constant $car is export = lambdaFn(
    'car', 'λxs.if-nil xs (λ_.error "cannot get car of nil") π2->1',
    -> TList:D $xs { case-List($xs,
        nil  => { $cXr-nil-error('car') },
        cons => $pi1o2
    ) }
);

constant $cdr is export = lambdaFn(
    'cdr', 'λxs.if-nil xs (λ_.error "cannot get cdr of nil") π2->2',
    -> TList:D $xs { case-List($xs,
        nil  => { $cXr-nil-error('cdr') },
        cons => $pi2o2
    ) }
);

constant $caar2 is export = lambdaFn('caar', 'B car car', $B($car, $car) );

constant $caar is export = $B($car, $car) does Definition(:symbol<caar>);
constant $cadr is export = $B($car, $cdr) does Definition(:symbol<cadr>);
constant $cdar is export = $B($cdr, $car) does Definition(:symbol<cdar>);
constant $cddr is export = $B($cdr, $cdr) does Definition(:symbol<cddr>);

constant $caaar is export = $B($car, $caar) does Definition(:symbol<caaar>);
constant $caadr is export = $B($car, $cadr) does Definition(:symbol<caadr>);
constant $cadar is export = $B($car, $cdar) does Definition(:symbol<cadar>);
constant $caddr is export = $B($car, $cddr) does Definition(:symbol<caddr>);
constant $cdaar is export = $B($cdr, $caar) does Definition(:symbol<cdaar>);
constant $cdadr is export = $B($cdr, $cadr) does Definition(:symbol<cdadr>);
constant $cddar is export = $B($cdr, $cdar) does Definition(:symbol<cddar>);
constant $cdddr is export = $B($cdr, $cddr) does Definition(:symbol<cdddr>);

constant $caaaar is export = $B($car, $caaar) does Definition(:symbol<caaaar>);
constant $caaadr is export = $B($car, $caadr) does Definition(:symbol<caaadr>);
constant $caadar is export = $B($car, $cadar) does Definition(:symbol<caadar>);
constant $caaddr is export = $B($car, $caddr) does Definition(:symbol<caaddr>);
constant $cadaar is export = $B($car, $cdaar) does Definition(:symbol<cadaar>);
constant $cadadr is export = $B($car, $cdadr) does Definition(:symbol<cadadr>);
constant $caddar is export = $B($car, $cddar) does Definition(:symbol<caddar>);
constant $cadddr is export = $B($car, $cdddr) does Definition(:symbol<cadddr>);
constant $cdaaar is export = $B($cdr, $caaar) does Definition(:symbol<cdaaar>);
constant $cdaadr is export = $B($cdr, $caadr) does Definition(:symbol<cdaadr>);
constant $cdadar is export = $B($cdr, $cadar) does Definition(:symbol<cdadar>);
constant $cdaddr is export = $B($cdr, $caddr) does Definition(:symbol<cdaddr>);
constant $cddaar is export = $B($cdr, $cdaar) does Definition(:symbol<cddaar>);
constant $cddadr is export = $B($cdr, $cdadr) does Definition(:symbol<cddadr>);
constant $cdddar is export = $B($cdr, $cddar) does Definition(:symbol<cdddar>);
constant $cddddr is export = $B($cdr, $cdddr) does Definition(:symbol<cddddr>);


# functions on TList

# we have to go through some extra hoops since this one's recursive
# (and we cannot use recursive references with constant declarations)
constant $yfoldl is export = -> {
    my $_foldl = -> &f, $acc, TList:D $xs {
        case-List($xs,
            nil  => $acc,
            cons => -> $head, TList:D $tail { $_foldl(&f, &f($acc, $head), $tail) }
        )
    };
    lambdaFn(
        'foldl', 'λf.λacc.λxs.(if-nil xs (K acc) (λhead.λtail.foldl f (f acc head) tail))',
        $_foldl
    );
}();

# Or we could use the Y combinator:
constant $foldl is export = $Y(-> &self { lambdaFn(
    'foldl', 'λself.λf.λacc.λxs.(if-nil xs λ_.acc λhead.λtail.self f (f acc head) tail)',
    -> &f, $acc, TList:D $xs {
        case-List( $xs,
            nil  => $acc,
            cons => -> $head, TList:D $tail { &self(&f, &f($acc, $head), $tail) }
        )
    }
)});

constant $foldl1 is export = lambdaFn(
    'foldl1', 'λf.λxs.NYI',
    -> &f, TList $xs {
        case-List($xs,
            nil => { die "cannot foldl1 nil" },
            cons => -> $hd, $tl { $foldl(&f, $hd, $tl) }
        )
    }
);

constant $reverse is export = lambdaFn(
    'reverse', '(foldl (C cons) nil)',
    -> TList:D $xs { $foldl( $swap-args($cons), $nil, $xs) }
);

# foldr in terms of foldl (and reverse)
constant $foldr-left-reverse is export = lambdaFn(
    'foldr-left-reverse', 'λf.λacc.λxs.foldl (C f) acc (reverse xs)',
    -> &f, $acc, TList:D $xs { $foldl( $swap-args(&f), $acc, $reverse($xs)) }
);

constant $foldr-rec is export = $Y(-> &self { lambdaFn(
    'foldr-rec', 'λself.λf.λacc.λxs.(if-nil xs λ_.acc λhead.λtail.f head (self f acc tail))',
    -> &f, $acc, TList:D $xs {
        case-List($xs,
            nil  => $acc,
            cons => -> $head, TList:D $tail { &f($head, &self(&f, $acc, $tail)) }
        )
    }
)});

# Even though the function is defined using recursion,
# the recursive call is in tail-position. Hence the resulting
# *process* is iterative (&todo actually is a continuation).
constant $foldr-iter is export = lambdaFn(
    'foldr-iter', 'λh.λinitial.Y (λself.λtodo.λxs.(if (nil? xs) (todo initial) (self (λacc.h (car xs) acc) (cdr xs)))) id',
    -> &h, $initial, TList:D $xs {
        $Y(-> &self { lambdaFn(
            'foldr-iter-stub', 'λself.λtodo.λxs.(if (nil? xs) (todo ' ~ $initial ~ ') (self (λacc.h (car xs) acc) (cdr xs)))',
            -> &todo, $xs {
                case-List($xs,
                    nil  => { &todo($initial) },
                    cons => -> $hd, TList:D $tl { &self( 
                        lambdaFn( Str, 'λacc.(' ~ &todo ~ ' (h ' ~ $hd ~ ' acc))',
                            -> $acc {
                                &todo(&h($hd, $acc));
                            }
                         ),
                         $tl
                     ) }
                )
            }
        )})($id, $xs);
    }
);
constant $foldr is export = $foldr-rec but name<foldr>;

constant $foldr1 is export = $Y(-> &self { lambdaFn(
    'foldr1', 'λself.λf.λxs.NYI',
    -> &f, TList:D $xs {
        case-List($xs,
            nil  => { die "cannot foldr1 nil" },
            cons => -> $hd, TList:D $tl {
                case-List($tl,
                    nil  => $hd,
                    cons => -> Mu, Mu { &f($hd, &self(&f, $tl)) }
                )
            }
        )
    }
)});


constant $map-foldr is export = lambdaFn(
    'map-foldr', 'λf.foldr (B cons f) nil',
    -> &f, TList:D $xs {
        $foldr(-> $x, $acc { $cons(&f($x), $acc) }, $nil, $xs)
    }
);

constant $map-rec is export = $Y(-> &self { lambdaFn(
    'map-rec', 'λself.λf.λxs.(if-nil xs λ_.nil λhead.λtail.(cons (f head) (self f tail)))',
    -> &f, TList:D $xs {
        case-List($xs,
            nil  => $nil,
            cons => -> $head, TList:D $tail { $cons(&f($head), &self(&f, $tail)) }
        )
    }
)});

constant $map-iter is export = lambdaFn(
    'map-iter', '((Y λself.λtodo.λxs.(if (nil? xs) (todo nil) (self (λresults.todo (cons (f (car xs)) results)) f (cdr xs)))) id)',
    $Y(-> &self { lambdaFn(
    'map-iter-stub', 'λself.λtodo.λxs.(if (nil? xs) (todo nil) (self (λresults.todo (cons (f (car xs)) results)) f (cdr xs)))',
    
        -> &todo {
            -> &f, $xs {
                case-List($xs,
                    nil  => { &todo($nil) },
                    cons => -> $head, TList:D $tail {
                         &self( -> $results { &todo($cons(&f($head), $results)) } )(&f, $tail) 
                     }
                )
            }
        }
    )}).($id)
);


constant $map is export = lambdaFn(
    'map', 'λf.λxs.map-rec f xs',
    -> &f, TList:D $xs { $map-rec(&f, $xs) }  # make a new one so we don't shadow the original's roles "lambda" and "name"
);

constant $length is export = lambdaFn(
    'length', 'λxs.foldl (λn.λ_.+ n 1) 0 xs',   # equiv to (foldl (λn.λ_.+ n 1) 0)
    -> TList:D $xs {
        $foldl(-> $n, $_ { $n + 1 }, 0, $xs)
    }
);

constant $append is export = lambdaFn(
    'append', 'λxs.λys.foldr cons ys xs',   # equiv to (foldr cons)
    -> TList:D $xs,  TList:D $ys {
        $foldr($cons, $ys, $xs) # using foldr because of the order of cons' parameters (and to maintain order of elems of xs)
    }
);

constant $filter is export = lambdaFn(
    'filter', 'λp.λxs.foldr (λx.λacc.((p x) (λ_.cons x acc) (λ_.acc)) _) nil xs',
    -> &p, TList $xs -->TList{ $foldr(
        -> $x, TList:D $acc -->TList{
            _if_( &p($x),
                { $cons($x, $acc) },
                $acc
            )
        },
        $nil,
        $xs
    )}
);

constant $except is export = lambdaFn(
    'except', 'λp.λxs.foldr (λx.λacc.((p x) (λ_.acc) (λ_.cons x acc)) _) nil xs',
    -> &p, TList $xs -->TList{ $foldr(
        -> $x, TList:D $acc -->TList{
            _if_( &p($x),
                $acc,
                { $cons($x, $acc) }
            )
        },
        $nil,
        $xs
    )}
);

constant $first is export = $Y(-> &self { lambdaFn(
    'first', 'λself.λp.λxs.(if (nil? xs) None (if (p (car xs)) (cons (car xs) nil) (self p (cdr xs))))',
    -> &p, TList:D $xs {
        case-List($xs,
            nil  => $None,
            cons => -> $head, TList:D $tail {
                 _if_( &p($head),
                     { $Some($head) },
                     { &self(&p, $tail) }
                 )
             }
        )
    }
)});

constant $___exists is export = lambdaFn(
    'exists', 'λp.λxs.Some? (first p xs)',
#   'exists', 'λp.(B not (B nil? (first p))',
    -> &p, TList:D $xs {
        #$is-Some($first(&p, $xs))
        case-Maybe($first(&p, $xs),
            None => $false,
            Some => $K1true
        )
    }
);

constant $exists is export = $Y(-> &self { lambdaFn(
    'exists', 'λself.λp.λxs.if (nil? xs) #false',
    -> &predicate, TList:D $xs -->TBool{ 
        case-List($xs,
            nil  => $false,
            cons => -> $hd, TList $tl -->TBool{
                _if_( &predicate($hd),
                    $true,
                    { &self(&predicate, $tl) }
                )
            }
        )
    }
    # alternative (not as efficient): foldl(-> $acc, $x { _if_($acc, $true, { &predicate($x) }) }, $false, $xs)
)});



# ->Str

constant $List2Str is export = lambdaFn(
    'List->Str', 'λxs.foldr (λx.λacc.(~ (~ (~ "(cons " (->Str x)) acc) ")")) "nil" xs',   # TODO: η-reduce list->str
    -> TList:D $xs {
        $foldr(
            -> $x, $acc {
                my $xStr = $x.?symbol // $x.?lambda // $x.perl;
                "(cons $xStr $acc)" 
            },
            'nil',
            $xs
        )
    }
);

constant $List2StrDense is export = $Y(-> &self { lambdaFn(
    'List->StrDense', '',   # TODO: η-reduce list->str
    -> TList:D $xs {
        my $inner = $foldl(
            -> $acc, $x {
                my $xStr = $x ~~ TList ?? &self($x) !! $x.?symbol // $x.?lambda // $x.perl;
                _if_(($acc eq '' ?? $true !! $false), # TODO: use $Str-eq('', $acc)
                    $xStr,
                    { $acc ~ ', ' ~ $xStr }
                );
            },
            '',
            $xs
        );
        '[' ~ $inner ~ ']';
    }
)});


# findFP-inMaybe_dbgXXX: (a -> Maybe a) -> List a
constant $findFP-inMaybe_dbgXXX is export = {
    my $arbiter = lambdaFn(
        Str, 'λv1.λm2.λnextStep.case m2 ((None (Some v1)) ((Some v2) (nextStep v2)))',
        -> TList $valuesBefore, TList $valuesAfter, &nextStep {
            case-Maybe($car($valuesAfter),
                None => $valuesBefore,
                Some => -> $nextVal { &nextStep($cons($nextVal, $valuesBefore)) }
            )
        }
    );
    lambdaFn(
        'findFP-inMaybe_dbgXXX', 'stepFn.error "NYI"',
        -> &stepFn {
            my &myStepFn = -> TList $valuesSoFar {
                case-List($valuesSoFar,
                    nil  => { die "should not happen" },
                    cons => -> $v, TList $vs {
                        $cons(&stepFn($v), $vs);
                    }
                );
            };
            my $fpSearch = $findFP($arbiter, &myStepFn);
            lambdaFn(
                Str, 'λstart.error "NYI"',
                -> $start {
                    # what to return on very 1st step, either nil or (cons start nil):
                    #my $initial = $nil;
                    my $initial = $cons($start, $nil);
                    case-Maybe(&stepFn($start),
                        None => $initial,
                        Some => -> $v1st { $fpSearch($cons($v1st, $initial)) }
                    )
                }
            )
        }
    )
}();


# findFP-inMaybe_dbg: (a -> Maybe a) -> List a
constant $findFP-inMaybe_dbg is export = lambdaFn(
    'findFP-inMaybe_dbg', 'stepFn.error "NYI"',
    -> &stepFn {
        # fpSearch: List -> Maybe List
        my $fpSearch = $findFP-inMaybe(-> TList $valuesSoFar {
            case-Maybe(&stepFn($car($valuesSoFar)),
                None => $None,
                Some => -> $next { $Some($cons($next, $valuesSoFar)) }
            )
        });
        lambdaFn(
            Str, 'λstart.error "NYI"',
            -> $start {
                my $startList = $cons($start, $nil);
                case-Maybe($fpSearch($startList),
                    None => $startList,
                    Some => $I
                )
            }
        )
    }
);
