use v6;

use Test;
use Test::Util;

use Lambda::Base;
use Lambda::Boolean;

use Lambda::ListADT;

plan 39;

{
    is_properLambdaFn($List2Str);

    is_properLambdaFn($nil);
    is_properLambdaFn($cons);

    is_properLambdaFn($is-nil);
}

{ # List->Str
    is $List2Str.name, 'List->Str', '$List.name -> "List->Str"';
    is $List2Str.Str,  'List->Str', '$List.Str -> "List->Str"';
}

{ # ctor nil
    is $nil.name,           'nil', '$nil.name -> "nil"';
    is $nil.Str,            'nil', '$nil.Str -> "nil"';
    does_ok $nil, TList,    'nil', :msg('nil is a TList in itself');
    is $List2Str($nil),     'nil', "($List2Str $nil) -> \"nil\"";
}

{ # ctor cons
    is $cons.name,          'cons', '$cons.name -> "cons"';
    is $cons.Str,           'cons', '$cons.Str -> "cons"';
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

{ # nil?, List2Str, .Str
    is $is-nil($nil), $true, '(nil? nil) -> #true';
    
    my $xs;
    my $ys;

    $xs = $cons($nil, $nil);
    is $is-nil($xs), $false, "(nil? $xs) -> $false";
    is $xs.Str,        '(cons nil nil)', '(cons nil nil).Str -> "(cons nil nil)"';
    is $List2Str($xs), '(cons nil nil)', "($List2Str (cons nil nil)) -> \"(cons nil nil)\"";


    $xs = $cons(5, $nil);
    is $is-nil($xs), $false, "(nil? $xs) -> #false";
    is $xs.Str,        '(cons 5 nil)', '(cons 5 nil).Str';
    is $List2Str($xs), '(cons 5 nil)', "($List2Str (cons 5 nil))";

    $ys = $cons('foo', $xs);
    is $is-nil($xs), $false, "(nil? $ys) -> $false";
    is $ys.Str,         '(cons "foo" (cons 5 nil))', "$ys.Str";
    is $List2Str($ys),  '(cons "foo" (cons 5 nil))', "($List2Str $ys)";
}
