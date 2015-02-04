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


# constructors

constant $nil is export = lambdaFn(
    'nil', 'λsel.sel #false _ _',
    -> &sel { &sel($false, Any, Any) }
) does TList;

constant $cons is export = lambdaFn(
    'cons', 'λx.λxs.λsel.sel #true x xs',
    -> $x, TList:D $xs {
            my $xStr = $x.?symbol // $x.?lambda // $x.perl;
            lambdaFn(
                Str, "cons $xStr $xs",
                -> &sel {
                    &sel($true, $x, $xs)
                }
            ) does TList
    }
);

constant $K1nil is export = $K1($nil);
constant $K2nil is export = $K2($nil);

# predicates

constant $is-nil is export = lambdaFn(
    'nil?', 'λxs.not (xs π3->1)',
    -> TList:D $xs { $not($xs($pi1o3)) }
);

# helper function if-nil, to reduce nr of calls to xs by half
constant $if-nil is export = lambdaFn(
    'if-nil', 'λxs.λwhenNil.λotherwise.xs λnotNil.λhead.λtail._if notNil (λ_.otherwise head tail) whenNil',
    -> TList:D $xs, &whenNil, &otherwise {
        $xs(-> $notNil, $head, $tail {
                $_if( $notNil,
                    -> $_ { &otherwise($head, $tail) },
                    &whenNil
                )
        })
    }
);

multi sub case-List(TList:D $list,
    :nil(&onNil)!,
    :cons(&onCons)!
) is export {
    #$list(&onNil, &onCons);
    $if-nil($list,
        -> Mu { &onNil },
        &onCons
    )
}

# projections

constant $car is export = lambdaFn(
    'car', 'λxs.if-nil xs (λ_.error "cannot get car of nil") π2->1',
    -> TList:D $xs {
        $if-nil( $xs,
               { die "cannot get car of nil" },
                 $pi1o2
        )
    }
);

constant $cdr is export = lambdaFn(
    'cdr', 'λxs.if-nil xs (λ_.error "cannot get cdr of nil") π2->2',
    -> TList:D $xs {
            $if-nil( $xs,
                   { die "cannot get cdr of nil" },
                     $pi2o2
            )
    }
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
        $if-nil( $xs,
                 $K($acc),
                 -> $head, TList:D $tail { $_foldl(&f, &f($acc, $head), $tail) })
    };
    lambdaFn(
        'foldl', 'λf.λacc.λxs.(if-nil xs (K acc) (λhead.λtail.foldl f (f acc head) tail))',
        $_foldl
    );
}();

# Or we could use the Y combinator:
constant $foldl is export = $Y(lambdaFn(
    'foldl', 'λself.λf.λacc.λxs.(if-nil xs λ_.acc λhead.λtail.self f (f acc head) tail)',
    -> &self {
        -> &f, $acc, TList:D $xs {
            $if-nil( $xs,
                     $K($acc),
                     -> $head, TList:D $tail { &self(&f, &f($acc, $head), $tail) }
            )
        }
    }
));

constant $reverse is export = lambdaFn(
    'reverse', '(foldl (C cons) nil)',
    -> TList:D $xs { $foldl( $swap-args($cons), $nil, $xs) }
);

# foldr in terms of foldl (and reverse)
constant $foldr-left-reverse is export = lambdaFn(
    'foldr-left-reverse', 'λf.λacc.λxs.foldl (C f) acc (reverse xs)',
    -> &f, $acc, TList:D $xs { $foldl( $swap-args(&f), $acc, $reverse($xs)) }
);

constant $foldr-rec is export = $Y( lambdaFn(
    'foldr-rec', 'λself.λf.λacc.λxs.(if-nil xs λ_.acc λhead.λtail.f head (self f acc tail))',
    -> &self {
        -> &f, $acc, TList:D $xs {
            $if-nil( $xs,
                     $K($acc),
                     -> $head, TList:D $tail { &f($head, &self(&f, $acc, $tail)) }
            )
        }
    }
));

# Even though the function is defined using recursion,
# the recursive call is in tail-position. Hence the resulting
# *process* is iterative (&todo actually is a continuation).
constant $foldr-iter is export = lambdaFn(
    'foldr-iter', 'λh.λinitial.Y (λself.λtodo.λxs.(if (nil? xs) (todo initial) (self (λacc.h (car xs) acc) (cdr xs)))) id',
    -> &h, $initial, TList:D $xs {
        $Y(lambdaFn(
            'foldr-iter-stub', 'λself.λtodo.λxs.(if (nil? xs) (todo ' ~ $initial ~ ') (self (λacc.h (car xs) acc) (cdr xs)))',
            -> &self {
                -> &todo, $xs {
                    $if-nil( $xs,
                        -> $_ { &todo($initial) },
                        -> $hd, TList $tl { &self( 
                            lambdaFn( Str, 'λacc.(' ~ &todo ~ ' (h ' ~ $hd ~ ' acc))',
                                -> $acc {
                                    &todo(&h($hd, $acc));
                                }
                             ),
                             $tl ) }
                    )
                }
            }
        ))($id, $xs);
    }
);
constant $foldr is export = $foldr-rec;

constant $map-foldr is export = lambdaFn(
    'map-foldr', 'λf.foldr (B cons f) nil',
    -> &f, TList:D $xs {
        $foldr(-> $x, $acc { $cons(&f($x), $acc) }, $nil, $xs)
    }
);

constant $map-rec is export = $Y( lambdaFn(
    'map-rec', 'λself.λf.λxs.(if-nil xs λ_.nil λhead.λtail.(cons (f head) (self f tail)))',
    -> &self {
        -> &f, TList:D $xs {
            $if-nil( $xs,
                     $K($nil),
                   -> $head, TList:D $tail { $cons(&f($head), &self(&f, $tail)) }
            )
        }
    }
));

constant $map-iter is export = lambdaFn(
    'map-iter', '((Y λself.λtodo.λxs.(if (nil? xs) (todo nil) (self (λresults.todo (cons (f (car xs)) results)) f (cdr xs)))) id)',
    $Y( lambdaFn(
        'map-iter-stub', 'λself.λtodo.λxs.(if (nil? xs) (todo nil) (self (λresults.todo (cons (f (car xs)) results)) f (cdr xs)))',
        -> &self {
            -> &todo {
                -> &f, $xs {
                    $if-nil( $xs,
                             -> $_ { &todo($nil) },
                             -> $head, TList:D $tail {
                                 &self( -> $results { &todo($cons(&f($head), $results)) } )(&f, $tail) 
                             }
                    )
                }
            }
        })).($id)
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
        $foldr($cons, $ys, $xs)
    }
);

constant $filter is export = lambdaFn(
    'filter', 'λp.λxs.foldr (λx.λacc.((p x) (λ_.cons x acc) (λ_.acc)) _) nil xs',
    -> &p, TList $xs -->TList{ $foldr(
        -> $x, TList $acc -->TList{
            $_if( &p($x),
                -> $_ { $cons($x, $acc) },
                -> $_ { $acc }
            )
        },
        $nil,
        $xs
    )}
);

constant $first is export = $Y( lambdaFn(
    'first', 'λself.λp.λxs.(if (nil? xs) None (if (p (car xs)) (cons (car xs) nil) (self p (cdr xs))))',
    -> &self {
        -> &p, TList:D $xs {
            $if-nil( $xs,
                     $K($None),
                     -> $head, TList:D $tail {
                         $_if( &p($head),
                             -> $_ { $Some($head) },
                             -> $_ { &self(&p, $tail) }
                         )
                     }
            )
        }
    }
));

constant $___exists is export = lambdaFn(
    'exists', 'λp.λxs.Some? (first p xs)',
#   'exists', 'λp.(B not (B nil? (first p))',
    -> &p, TList:D $xs {
        $is-Some($first(&p, $xs))
    }
);

constant $exists is export = $Y( lambdaFn(
    'exists', 'λself.λp.λxs.if (nil? xs) #false',
    -> &self {
        -> &predicate, TList:D $xs -->TBool{ 
            $if-nil($xs,
                    $K1false,
                    -> $hd, TList $tl -->TBool{
                        $_if( &predicate($hd),
                            $K1true,
                            -> $_ { &self(&predicate, $tl) }
                        )
                    })
        }
    }
    # alternative (not as efficient): foldl(-> $acc, $x { $_if($acc, -> $_ {$true}, -> $_ {&predicate($x)}) }, $false, $xs)
));



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
