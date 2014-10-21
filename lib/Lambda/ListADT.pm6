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
    method Str { list2str(self) }
}


# constructors

constant $nil is export = lambdaFn(
    'nil', 'λsel.sel #false _ _',
    -> &sel { &sel($false, Any, Any) }
) does TList;

constant $cons is export = lambdaFn(
    'cons', 'λx.λxs.λsel.sel #true x xs',
    -> $x, TList:D $rest { 
        lambdaFn(
            Str, "λxs.λsel.sel #true $x xs",
            -> &sel { &sel($true, $x, $rest) }
        ) does TList
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
    $Y(-> $self {
        -> $f, $acc, $xs {
            $_if( $is-nil($xs),
                { $acc },
                { $self($f, $f($car($xs), $acc), $cdr($xs)) })    }    })   # TODO: swap args to f
);

constant $reverse is export = lambdaFn(
    'reverse', '(foldl cons nil)',
    -> $xs { $foldl($cons, $nil, $xs) }
);

# (δ foldr λf.λacc.λxs.foldl f acc (reverse xs))
sub foldr(&f, $acc, TList:D $xs) is export {
    $foldl(&f, $acc, $reverse($xs));
}

# (δ foldr-rec λf.λacc.λxs.(if (nil? xs) acc (f (car xs) (foldr-rec f acc (cdr xs))))))
sub foldr-rec(&f, $acc, TList:D $xs) is export {
    $_if($is-nil($xs),
        {$acc},
        {&f($car($xs), foldr-rec(&f, $acc, $cdr($xs)))})
}

# (δ map-rev-iter λr.λf.λxs.(if (nil? xs) r (map-iter (cons (f (car xs)) r) f (cdr xs))))
# (δ map-rev-iter λr.λf.foldl (λx.cons (f x)) nil)
sub map-rev-iter($result, &f, TList:D $xs) {
#    $is-nil($xs)
#        ?? $result
#        !! map-rev-iter(cons(&f($car($xs)), $result), &f, $cdr($xs));
    $foldl(-> $x, $acc { $cons(&f($x), $acc) }, $nil, $xs);
}

# (δ map-iter λf.foldr (λx.cons (f x)) nil)
sub map-iter(&f, TList:D $xs) {
    foldr(-> $x, $acc { $cons(&f($x), $acc) }, $nil, $xs);
}

# (δ map-rec λr.λf.λxs (if (nil? xs) xs (cons (f (car xs)) (map-rec f (cdr xs)))))
sub map-rec(&f, TList:D $xs) {
    $_if($is-nil($xs),
        {$nil},
        {$cons(&f($car($xs)), map-rec(&f, $cdr($xs)))})
}

sub map(&f, TList:D $xs) is export {
    #$reverse(map-rev-iter($nil, &f, $xs));
    map-iter(&f, $xs);
    #map-rec(&f, $xs);
}

# (δ length λxs.foldl (λ_.λn.+ n 1) 0 xs)
sub length(TList:D $xs) is export {
    $foldl(-> $_, $n { $n + 1 }, 0, $xs)
}

# (δ filter λp.foldr (λx.λacc.($_if (p x) λ_.(cons x acc) λ_.acc)) nil)
sub filter(&predicate, TList:D $xs) is export {
    foldr(
        -> $x, $acc {
            $_if(&predicate($x),
                {$cons($x, $acc)},
                {$acc})
        }, 
        $nil,
        $xs);
}

sub exists(&predicate, TList:D $xs) is export {
    #foldl(-> $x, $acc { $_if($acc, {$true}, {&predicate($x)}) }, $false, $xs)
    $_if($is-nil($xs),
        { $false },
        { $_if(&predicate($car($xs)), {$true}, {exists(&predicate, $cdr($xs))}) })
}



# ->str

constant $list2str is export = lambdaFn(
    'list->str', 'λxs.foldr (λx.λacc.(~ (~ "(cons " (->str x)) acc)) "nil" xs',   # TODO: η-reduce list->str
    -> TList:D $xs {
        foldr(
            -> $x, $acc { "(cons $x $acc)" },
            'nil',
            $xs
        )
    }
);

my sub list2str(TList:D $xs) {
    #foldr(-> $x, $acc { "(cons $x $acc)" }, 'nil', $xs);
    $list2str($xs)
}
