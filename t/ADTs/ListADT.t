use v6;
use Test;
use Test::Util;
use Test::Util_Lambda;

use Lambda::Boolean;


# module under test:
use Lambda::ListADT;

plan 33;


# ->Str -----------------------------------------------------------------------

{ # List->Str
    is_properLambdaFn $List2Str, 'List->Str';
}


# nil -------------------------------------------------------------------------

{ # ctor nil
    is_properLambdaFn $nil, 'nil';

    does_ok $nil, TList,    'nil', :msg('nil is a TList in itself');
    is $List2Str($nil),     'nil', "($List2Str $nil)";
}

{ # predicate nil?, List2Str, .Str
    is_properLambdaFn $is-nil, 'nil?';

    is $is-nil($nil), $true, '(nil? nil)';
    
    my $xs;
    my $ys;

    $xs = $cons($nil, $nil);
    is $is-nil($xs), $false, "(nil? $xs)";
    is $xs.Str,        '(cons nil nil)', '(cons nil nil).Str"';
    is $List2Str($xs), '(cons nil nil)', "($List2Str (cons nil nil))";


    $xs = $cons(5, $nil);
    is $is-nil($xs), $false, "(nil? $xs)";
    is $xs.Str,        '(cons 5 nil)', '(cons 5 nil).Str';
    is $List2Str($xs), '(cons 5 nil)', "($List2Str (cons 5 nil))";

    $ys = $cons('foo', $xs);
    is $is-nil($xs), $false, "(nil? $ys)";
    is $ys.Str,         '(cons "foo" (cons 5 nil))', "$ys.Str";
    is $List2Str($ys),  '(cons "foo" (cons 5 nil))', "($List2Str $ys)";
}


# cons ------------------------------------------------------------------------

{ # ctor cons
    is_properLambdaFn $cons, 'cons';

    doesnt_ok $cons, TList, 'cons', :msg('cons is NOT a TList in itself');
    dies_ok { $List2Str($cons) }, "($List2Str $cons) yields error";

    my ($xs, $xsStr);

    $xs = $cons($nil, $nil);
    $xsStr = '(cons nil nil)'; # expected
    is $List2Str($xs), $xsStr, "($List2Str $xsStr)";
    does_ok $xs, TList, "$xs";
    is_validLambda($xs);

    $xs = $cons(5, $nil);
    $xsStr = '(cons 5 nil)'; # expected
    is $List2Str($xs), $xsStr, "($List2Str $xsStr)";
    does_ok $xs, TList, "$xs";
    is_validLambda($xs);

    $xs = $cons("foo", $nil);
    $xsStr = '(cons "foo" nil)'; # expected
    is $List2Str($xs), $xsStr, "($List2Str $xsStr)";
    does_ok $xs, TList, "$xs";
    is_validLambda($xs);

    $xs = $cons(42, $cons("bar", $nil));
    $xsStr = '(cons 42 (cons "bar" nil))'; # expected
    is $List2Str($xs), $xsStr, "($List2Str $xsStr)";
    does_ok $xs, TList, "$xs";
    is_validLambda($xs);

    my $ys = $xs; # list of list
    $xs = $cons($xs, $xs);
    $xsStr = '(cons (cons 42 (cons "bar" nil)) (cons 42 (cons "bar" nil)))'; # expected
    is $List2Str($xs), $xsStr, "($List2Str $xsStr)";
    does_ok $xs, TList, "$xs";
    is_validLambda($xs);
}
