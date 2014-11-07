use v6;

use Lambda::Base;
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


# predicates

constant $is-nil is export = lambdaFn(
    'nil?', 'λxs.not (xs π3->1)',
    -> TList:D $xs { $not($xs($pi1o3)) }
);


# projections

constant $car is export = lambdaFn(
    'car', 'λxs.if (nil? xs) (error "cannot get car of nil") (xs π3->2)',
    -> TList:D $xs {
        $_if( $is-nil($xs),
            { die "cannot get car of nil" },
            { $xs.($pi2o3) }
        )
    }
);

constant $cdr is export = lambdaFn(
    #'cdr', 'λxs.if (nil? xs) (error "cannot get cdr of nil") (xs π3->3)',
    'cdr', 'λxs.((nil? xs) (λ_.error "cannot get cdr of nil") (λ_.xs π3->3)) _',
    -> TList:D $xs {
            $_if( $is-nil($xs),
                { die "cannot get cdr of nil" },
                { $xs($pi3o3) }
            )
    }
);

constant $caar is export = lambdaFn( 'caar', 'B car car', $B($car, $car) );
constant $cadr is export = lambdaFn( 'cadr', 'B car cdr', $B($car, $cdr) );
constant $cdar is export = lambdaFn( 'cdar', 'B cdr car', $B($cdr, $car) );
constant $cddr is export = lambdaFn( 'cddr', 'B cdr cdr', $B($cdr, $cdr) );

constant $caaar is export = lambdaFn( 'caaar', 'B car caar', $B($car, $caar) );
constant $caadr is export = lambdaFn( 'caadr', 'B car cadr', $B($car, $cadr) );
constant $cadar is export = lambdaFn( 'cadar', 'B car cdar', $B($car, $cdar) );
constant $caddr is export = lambdaFn( 'caddr', 'B car cddr', $B($car, $cddr) );
constant $cdaar is export = lambdaFn( 'cdaar', 'B cdr caar', $B($cdr, $caar) );
constant $cdadr is export = lambdaFn( 'cdadr', 'B cdr cadr', $B($cdr, $cadr) );
constant $cddar is export = lambdaFn( 'cddar', 'B cdr cdar', $B($cdr, $cdar) );
constant $cdddr is export = lambdaFn( 'cdddr', 'B cdr cddr', $B($cdr, $cddr) );


constant $caaaar is export = lambdaFn( 'caaaar', 'B car caaar', $B($car, $caaar) );
constant $caaadr is export = lambdaFn( 'caaadr', 'B car caadr', $B($car, $caadr) );
constant $caadar is export = lambdaFn( 'caadar', 'B car cadar', $B($car, $cadar) );
constant $caaddr is export = lambdaFn( 'caaddr', 'B car caddr', $B($car, $caddr) );
constant $cadaar is export = lambdaFn( 'cadaar', 'B car cdaar', $B($car, $cdaar) );
constant $cadadr is export = lambdaFn( 'cadadr', 'B car cdadr', $B($car, $cdadr) );
constant $caddar is export = lambdaFn( 'caddar', 'B car cddar', $B($car, $cddar) );
constant $cadddr is export = lambdaFn( 'cadddr', 'B car cdddr', $B($car, $cdddr) );
constant $cdaaar is export = lambdaFn( 'cdaaar', 'B cdr caaar', $B($cdr, $caaar) );
constant $cdaadr is export = lambdaFn( 'cdaadr', 'B cdr caadr', $B($cdr, $caadr) );
constant $cdadar is export = lambdaFn( 'cdadar', 'B cdr cadar', $B($cdr, $cadar) );
constant $cdaddr is export = lambdaFn( 'cdaddr', 'B cdr caddr', $B($cdr, $caddr) );
constant $cddaar is export = lambdaFn( 'cddaar', 'B cdr cdaar', $B($cdr, $cdaar) );
constant $cddadr is export = lambdaFn( 'cddadr', 'B cdr cdadr', $B($cdr, $cdadr) );
constant $cdddar is export = lambdaFn( 'cdddar', 'B cdr cddar', $B($cdr, $cddar) );
constant $cddddr is export = lambdaFn( 'cddddr', 'B cdr cdddr', $B($cdr, $cdddr) );


# functions on TList

# we have to go through some extra hoops since this one's recursive
# (and we cannot use recursive references with constant declarations)
constant $yfoldl is export = -> {
    my $_foldl = -> &f, $acc, TList:D $xs {
        $_if( $is-nil($xs),
            { $acc },
            { $_foldl(&f, &f($car($xs), $acc), $cdr($xs)) })   # TODO: swap args to f
    };
    lambdaFn(
        'foldl', 'λf.λacc.λxs.(if (nil? xs) acc (foldl f (f acc (car xs)) (cdr xs)))',
        $_foldl
    );
}();

# Or we could use the Y combinator:
constant $foldl is export = $Y( lambdaFn(
    'foldl', 'λself.λf.λacc.λxs.(if (nil? xs) acc (self f (f acc (car xs)) (cdr xs)))',
    -> &self {
        -> &f, $acc, TList:D $xs {
            $_if( $is-nil($xs),
                { $acc },
                { &self(&f, &f($acc, $car($xs)), $cdr($xs)) })    }    }
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
    'foldr-rec', 'λself.λf.λacc.λxs.(if (nil? xs) acc (f (car xs) (self f acc (cdr xs))))',
    -> &self {
        -> &f, $acc, TList:D $xs {
            $_if( $is-nil($xs),
                { $acc },
                { &f($car($xs), &self(&f, $acc, $cdr($xs))) })
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
                    $_if( $is-nil($xs),
                        { &todo($initial) },
                        { &self( 
                            lambdaFn( Str, 'λacc.(' ~ &todo ~ ' (h ' ~ $car($xs) ~ ' acc))',
                                -> $acc {
                                    &todo(&h($car($xs), $acc));
                                }
                             ),
                             $cdr($xs) ) }
                    )
                }
            }
        ))($id, $xs);
    }
);
constant $foldr is export = $foldr-rec;

constant $map-foldr is export = lambdaFn(
    'map-foldr', 'λf.foldr (λx.cons (f x)) nil',
    -> &f, TList:D $xs {
        $foldr(-> $x, $acc { $cons(&f($x), $acc) }, $nil, $xs)
    }
);

constant $map-rec is export = $Y( lambdaFn(
    'map-rec', 'λself.λf.λxs.(if (nil? xs) xs (cons (f (car xs)) (self f (cdr xs))))',
    -> &self {
        -> &f, TList:D $xs {
            $_if( $is-nil($xs),
                { $nil },
                { $cons(&f($car($xs)), &self(&f, $cdr($xs))) })
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
                    $_if( $is-nil($xs),
                        { &todo($nil) },
                        { &self( -> $results { &todo($cons(&f($car($xs)), $results)) } )(&f, $cdr($xs)) } )
                }
            }
        })).($id)
);


constant $map is export = lambdaFn(
    'map', 'λf.λxs.map-foldr f xs',
    -> &f, TList:D $xs { $map-foldr(&f, $xs) }  # make a new one so we don't shadow the original's roles "lambda" and "name"
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
    -> &p, $xs { $foldr(
        -> $x, $acc {
            $_if( &p($x),
                { $cons($x, $acc) },
                { $acc })
        },
        $nil,
        $xs
    )}
);

constant $first is export = $Y( lambdaFn(
    'first', 'λself.λp.λxs.(if (nil? xs) None (if (p (car xs)) (cons (car xs) nil) (self p (cdr xs))))',
    -> &self {
        -> &p, TList:D $xs {
            $_if( $is-nil($xs),
                { $None },
                { $_if( &p($car($xs)),
                    { $Some($car($xs)) },
                    { &self(&p, $cdr($xs)) })
                })
        }
    }
));

constant $exists is export = lambdaFn(
    'exists', 'λp.λxs.Some? (first p xs)',
#   'exists', 'λp.(B not (B nil? (first p))',
    -> &p, TList:D $xs {
        $is-Some($first(&p, $xs))
    }
);

constant $___exists is export = $Y( lambdaFn(
    'exists', 'λself.λp.λxs.if (nil? xs) #false',
    -> &self {
        -> &predicate, TList:D $xs { 
            $_if( $is-nil($xs),
                { $false },
                { $_if( &predicate($car($xs)),
                    { $true },
                    { &self(&predicate, $cdr($xs)) })
                })
        }
    }
    # alternative (not as efficient): foldl(-> $acc, $x { $_if($acc, {$true}, {&predicate($x)}) }, $false, $xs)
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
