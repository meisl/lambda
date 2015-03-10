use v6;
use Test;
use Test::Util;
use Test::Util_Lambda;

use Lambda::Boolean;


# module under test (the cXr-functions):
use Lambda::ListADT;

plan 55;


{ # car
    is_properLambdaFn $car, 'car';

    doesnt_ok $car, TList, 'car', :msg('car is NOT a TList in itself');
    dies_ok {$List2Str($car) }, "($List2Str car) yields error";

    dies_ok({ $car($nil) }, 'car on nil yields error');

    my $xs = $cons(23, $nil);
    is $car($xs), 23, 'car on 1-elem list extracts first elem';

    $xs = $cons(42, $xs);
    is $car($xs), 42, 'car on 2-elem list extracts first elem';
}

{ # cdr
    is_properLambdaFn $cdr, 'cdr';

    doesnt_ok $cdr, TList, 'cdr', :msg('cdr is NOT a TList in itself');
    dies_ok {$List2Str($cdr) }, "($List2Str cdr) yields error";

    dies_ok({ $cdr($nil) }, 'cdr on nil yields error');

    my $xs = $cons(23, $nil);
    is $cdr($xs), $nil, 'cdr on 1-elem list yields nil';

    my $ys = $cons(42, $xs);
    is $cdr($ys), $xs, 'cdr on 2-elem list extracts tail list';
}

{ # caar
    is_properLambdaFn $caar, 'caar';

    dies_ok({ $caar($nil) }, 'caar on nil yields error');

    my $xs = $cons(23, $nil);
    dies_ok({ $caar($xs) }, 'caar on 1-elem list yields error if first elem is not a list');

    $xs = $cons(42, $xs);
    dies_ok({ $caar($xs) }, 'caar on 2-elem list yields error if first elem is not a list');
    
    $xs = $cons($xs, $nil);
    is $caar($xs), 42, 'caar extracts first elem of the list at the first elem (of outer list)';
}

{ # cadr
    is_properLambdaFn $cadr, 'cadr';

    dies_ok({ $cadr($nil) }, 'cadr on nil yields error');

    my $xs = $cons(23, $nil);
    dies_ok({ $cadr($xs) }, 'cadr on 1-elem list yields error');

    $xs = $cons(42, $xs);
    is $cadr($xs), 23, 'cadr extracts 2nd elem (a simple elem)';
    
    my $ys = $cons(5, $cons($xs, $nil));
    is $cadr($ys), $xs, 'cadr extracts 2nd elem (a list)';
}

{ # cdar
    is_properLambdaFn $cdar, 'cdar';

    dies_ok({ $cdar($nil) }, 'cdar on nil yields error');

    my $xs = $cons(23, $nil);
    dies_ok({ $cdar($xs) }, 'cdar on 1-elem list yields error if 1st elem aint a list');

    my $ys = $cons($cons("foo", $xs), $cons("bar", $nil));
    is $cdar($ys), $xs, 'cadr extracts tail of 1st elem';
}

{ # cddr
    is_properLambdaFn $cddr, 'cddr';

    dies_ok({ $cddr($nil) }, 'cddr on nil yields error');

    my $xs = $cons(23, $nil);
    dies_ok({ $cddr($xs) }, 'cddr on 1-elem list yields error');

    $xs = $cons(42, $xs); # xs: (cons 42 (cons 23 nil))
    is $cddr($xs), $nil, 'cddr on 2-elem list yields nil';

    my $ys = $cons($cons("foo", $nil), $cons("bar", $xs));
    is $cddr($ys), $xs, 'cddr extracts tail of tail';
}


{
    is_properLambdaFn $caaar, 'caaar';
    is_properLambdaFn $caadr, 'caadr';
    is_properLambdaFn $cadar, 'cadar';
    is_properLambdaFn $caddr, 'caddr';
    is_properLambdaFn $cdaar, 'cdaar';
    is_properLambdaFn $cdadr, 'cdadr';
    is_properLambdaFn $cddar, 'cddar';
    is_properLambdaFn $cdddr, 'cdddr';

    is_properLambdaFn $caaaar, 'caaaar';
    is_properLambdaFn $caaadr, 'caaadr';
    is_properLambdaFn $caadar, 'caadar';
    is_properLambdaFn $caaddr, 'caaddr';
    is_properLambdaFn $cadaar, 'cadaar';
    is_properLambdaFn $cadadr, 'cadadr';
    is_properLambdaFn $caddar, 'caddar';
    is_properLambdaFn $cadddr, 'cadddr';
    is_properLambdaFn $cdaaar, 'cdaaar';
    is_properLambdaFn $cdaadr, 'cdaadr';
    is_properLambdaFn $cdadar, 'cdadar';
    is_properLambdaFn $cdaddr, 'cdaddr';
    is_properLambdaFn $cddaar, 'cddaar';
    is_properLambdaFn $cddadr, 'cddadr';
    is_properLambdaFn $cdddar, 'cdddar';
    is_properLambdaFn $cddddr, 'cddddr';
}
