use v6;

use Lambda::Base;
use Lambda::Boolean;

module Lambda::ListADT;


# (δ sel1of3 λa.λb.λc.a)
sub sel1of3($a, $b, $c) is export { $a }

# (δ sel2of3 λa.λb.λc.b)
sub sel2of3($a, $b, $c) is export { $b }

# (δ sel3of3 λa.λb.λc.c)
sub sel3of3($a, $b, $c) is export { $c }

# data List = nil
#           | cons car:_ cdr:List
role TList is export {

    my @closures = @();
    has &.toStrClosure;
    submethod BUILD(:&toStrClosure) {
        &!toStrClosure = &toStrClosure;
        @closures.push(&toStrClosure);
        #note '>>>> TList.BUILD: ' ~ @closures.elems;
    }
    method Str { &!toStrClosure() }
}


# constructors

constant $nil is export = lambdaFn(
    'nil', 'λsel.sel #false _ _',
    -> &sel { &sel($false, Any, Any) }
) does TList({ 'nil' });

constant $cons is export = lambdaFn(
    'cons', 'λx.λxs.λsel.sel #true x xs',
    -> $x, TList:D $xs { 
            (-> &sel { &sel($true, $x, $xs) }
        ) does TList({   # must pass this closure to the role since closing over with just a 'but' or 'does' silently fails
            my $xStr = $x.?name // $x.?lambda // $x.perl;
            "(cons $xStr $xs)";
        })
    }
);


# predicates

constant $is-nil is export = lambdaFn(
    'nil?', 'λxs.not (xs sel1of3)',
    -> TList:D $xs { $not($xs.(&sel1of3)) }
);


# projections

constant $car is export = lambdaFn(
    'car', 'λxs.if (nil? xs) (error "cannot get car of nil") (xs sel2of3)',
    -> TList:D $xs {
        $_if($is-nil($xs),
            {die "cannot get car of nil"},
            {$xs.(&sel2of3)})
    }
);

constant $cdr is export = lambdaFn(
    #'cdr', 'λxs.if (nil? xs) (error "cannot get cdr of nil") (xs sel3of3)',
    'cdr', 'λxs.((nil? xs) (λ_.error "cannot get cdr of nil") (λ_.xs sel3of3)) _',
    -> TList:D $xs {
            $_if($is-nil($xs),
            {die "cannot get cdr of nil"},
            {$xs(&sel3of3)})
    }
);

# (δ caar λxs.car (car xs))
sub caar(TList:D $xs) is export { $car($car($xs)) }
sub cadr(TList:D $xs) is export { $car($cdr($xs)) }
sub cdar(TList:D $xs) is export { $cdr($car($xs)) }
sub cddr(TList:D $xs) is export { $cdr($cdr($xs)) }
sub caddr(TList:D $xs) is export { $car(cddr($xs)) }
sub cdddr(TList:D $xs) is export { $cdr(cddr($xs)) }
sub cadddr(TList:D $xs) is export { $car(cdddr($xs)) }


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
        'foldl',          'λf.λacc.λxs (if (nil? xs) acc (foldl f (f acc (car xs)) (cdr xs)))',
        #'foldl', 'Y λself.λf.λacc.λxs (if (nil? xs) acc (self f (f acc (car xs)) (cdr xs)))',
        $_foldl
    );
}();

# Or we could use the Y combinator:
constant $foldl is export = lambdaFn(
    'foldl', 'Y λself.λf.λacc.λxs (if (nil? xs) acc (self f (f acc (car xs)) (cdr xs)))',
    $Y(-> &self {
        -> &f, $acc, TList:D $xs {
            $_if( $is-nil($xs),
                { $acc },
                { &self(&f, &f($acc, $car($xs)), $cdr($xs)) })    }    })
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

constant $foldr-rec is export = lambdaFn(
    'foldr-rec', '(Y λself.λf.λacc.λxs.(if (nil? xs) acc (f (car xs) (self f acc (cdr xs))))))',
    $Y(-> &self {
        -> &f, $acc, TList:D $xs {
            $_if( $is-nil($xs),
                { $acc },
                { &f($car($xs), &self(&f, $acc, $cdr($xs))) })
        }
    })
);

# Even though the function is defined using recursion,
# the recursive call is in tail-position. Hence the resulting
# *process* is iterative (&todo actually is a continuation).
constant $foldr-iter is export = lambdaFn(
    'foldr-iter', 'λh.initial.λxs.Y λself.λtodo.λxs.(if (nil? xs) (todo initial) (self (λacc.h (car xs) acc) (cdr xs))',
    -> &h, $acc, TList:D $xs {
        $Y(lambdaFn(
            Str, 'λself.λtodo.λxs.(if (nil? xs) (todo ' ~ $acc ~ ') (self (λacc.h (car xs) acc) (cdr xs))',
            -> &self {
                -> &todo, $xs {
                    $_if( $is-nil($xs),
                        { &todo($acc) },
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

constant $map-rec is export = lambdaFn(
    'map-rec', 'Y λself.λr.λf.λxs (if (nil? xs) xs (cons (f (car xs)) (self f (cdr xs))))',
    $Y(-> &self {
        -> &f, TList:D $xs {
            $_if( $is-nil($xs),
                { $nil },
                { $cons(&f($car($xs)), &self(&f, $cdr($xs))) })
        }
    })
);

constant $map-iter is export = lambdaFn(
    'map-iter', '((Y λself.λtodo.λxs.(if (nil? xs) (todo nil) (self (λresults.todo (cons (f (car xs)) results)) f (cdr xs)))) id)',
    $Y(-> &self {
        -> &todo {
            -> &f, $xs {
                $_if( $is-nil($xs),
                    { &todo($nil) },
                    { &self( -> $results { &todo($cons(&f($car($xs)), $results)) } )(&f, $cdr($xs)) } )
            }
        }
    })($id)
);


constant $map is export = lambdaFn(
    'map', 'map-???',
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

constant $first is export = lambdaFn(
    'first', 'Y λself.λp.λxs.(if (nil? xs) nil (if (p (car xs)) (cons (car xs) nil) (self p (cdr xs))))',
    $Y(-> &self {
        -> &p, TList:D $xs {
            $_if( $is-nil($xs),
                { $nil },
                { $_if( &p($car($xs)),
                    { $cons($car($xs), $nil) },
                    { &self(&p, $cdr($xs)) })
                })
        }
    })
);

constant $exists is export = lambdaFn(
    'exists', 'λp.λxs.not (nil? (first p xs))',
#   'exists', 'λp.(B not (B nil? (first p))',
    -> &p, TList:D $xs {
        $not($is-nil($first(&p, $xs)))
    }
);

constant $___exists is export = lambdaFn(
    'exists', 'Y λself.λp.λxs.if (nil? xs) #false',
    $Y(-> &self{
        -> &predicate, TList:D $xs { 
            $_if( $is-nil($xs),
                { $false },
                { $_if( &predicate($car($xs)),
                    { $true },
                    { &self(&predicate, $cdr($xs)) })
                })
        }
    })
    # alternative (not as efficient): foldl(-> $acc, $x { $_if($acc, {$true}, {&predicate($x)}) }, $false, $xs)
);



# ->str

constant $list2str is export = lambdaFn(
    'list->str', 'λxs.foldr (λx.λacc.(~ (~ "(cons " (->str x)) acc)) "nil" xs',   # TODO: η-reduce list->str
    -> TList:D $xs {
        $foldr(
            -> $x, $acc { "(cons $x $acc)" },
            'nil',
            $xs
        )
    }
);
