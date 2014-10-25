use v6;

use Test;
use Test::Util;

use Lambda::Base;
use Lambda::Boolean;
use Lambda::ListADT;

plan 111;

{
    is_properLambdaFn($car);
    is_properLambdaFn($cdr);

    is_properLambdaFn($caar);
    is_properLambdaFn($cadr);
    is_properLambdaFn($cdar);
    is_properLambdaFn($cddr);

    is_properLambdaFn($caaar);
    is_properLambdaFn($caadr);
    is_properLambdaFn($cadar);
    is_properLambdaFn($caddr);
    is_properLambdaFn($cdaar);
    is_properLambdaFn($cdadr);
    is_properLambdaFn($cddar);
    is_properLambdaFn($cdddr);

    is_properLambdaFn($caaaar);
    is_properLambdaFn($caaadr);
    is_properLambdaFn($caadar);
    is_properLambdaFn($caaddr);
    is_properLambdaFn($cadaar);
    is_properLambdaFn($cadadr);
    is_properLambdaFn($caddar);
    is_properLambdaFn($cadddr);
    is_properLambdaFn($cdaaar);
    is_properLambdaFn($cdaadr);
    is_properLambdaFn($cdadar);
    is_properLambdaFn($cdaddr);
    is_properLambdaFn($cddaar);
    is_properLambdaFn($cddadr);
    is_properLambdaFn($cdddar);
    is_properLambdaFn($cddddr);
}


{ # car
    dies_ok({ $car($nil) }, 'car on nil yields error');

    my $xs = $cons(23, $nil);
    is $car($xs), 23, 'car on 1-elem list extracts first elem';

    $xs = $cons(42, $xs);
    is $car($xs), 42, 'car on 2-elem list extracts first elem';
}

{ # cdr
    dies_ok({ $cdr($nil) }, 'cdr on nil yields error');

    my $xs = $cons(23, $nil);
    is $cdr($xs), $nil, 'car on 1-elem list yields nil';

    my $ys = $cons(42, $xs);
    is $cdr($ys), $xs, 'car on 2-elem list extracts tail list';
}

{ # caar
    dies_ok({ $caar($nil) }, 'caar on nil yields error');

    my $xs = $cons(23, $nil);
    dies_ok({ $caar($xs) }, 'caar on 1-elem list yields error if first elem is not a list');

    $xs = $cons(42, $xs);
    dies_ok({ $caar($xs) }, 'caar on 2-elem list yields error if first elem is not a list');
    
    $xs = $cons($xs, $nil);
    is $caar($xs), 42, 'caar extracts first elem of the list at the first elem (of outer list)';
}

{ # cadr
    dies_ok({ $cadr($nil) }, 'cadr on nil yields error');

    my $xs = $cons(23, $nil);
    dies_ok({ $cadr($xs) }, 'cadr on 1-elem list yields error');

    $xs = $cons(42, $xs);
    is $cadr($xs), 23, 'cadr extracts 2nd elem (a simple elem)';
    
    my $ys = $cons(5, $cons($xs, $nil));
    is $cadr($ys), $xs, 'cadr extracts 2nd elem (a list)';
}

{ # cdar
    dies_ok({ $cdar($nil) }, 'cdar on nil yields error');

    my $xs = $cons(23, $nil);
    dies_ok({ $cdar($xs) }, 'cdar on 1-elem list yields error if 1st elem aint a list');

    my $ys = $cons($cons("foo", $xs), $cons("bar", $nil));
    is $cdar($ys), $xs, 'cadr extracts tail of 1st elem';
}

{ # cddr
    dies_ok({ $cddr($nil) }, 'cddr on nil yields error');

    my $xs = $cons(23, $nil);
    dies_ok({ $cddr($xs) }, 'cddr on 1-elem list yields error');

    $xs = $cons(42, $xs); # xs: (cons 42 (cons 23 nil))
    is $cddr($xs), $nil, 'cddr on 2-elem list yields nil';

    my $ys = $cons($cons("foo", $nil), $cons("bar", $xs));
    is $cddr($ys), $xs, 'cddr extracts tail of tail';
}
