use v6;
use Test;
use Test::Util;
use Test::Util_Lambda;

use Lambda::BaseP6;
use Lambda::Boolean;
use Lambda::P6Currying;


# module under test:
use Lambda::TermADT;

plan 147;


# Term-eq ---------------------------------------------------------------------

{
    sub test-eq(TTerm $t1, TTerm $t2, TBool $expected) {
        subtest({
            my $msg;

            $msg = "'{$Term2source($t1)} should " ~ ($expected === $true ?? '' !! 'NOT ') ~ "equal {$Term2source($t2)}";
            is $Term-eq($t1, $t2), $expected, $msg;
            # (in-)equality is symmetric:
            $msg = "'{$Term2source($t2)} should " ~ ($expected === $true ?? '' !! 'NOT ') ~ "equal {$Term2source($t1)}";
            is $Term-eq($t2, $t1), $expected, $msg;
        });
    }

    my $x = $VarT('x');
    my $y = $VarT('y');
    my $c1 = $ConstT(5);
    my $c2 = $ConstT('5');
    my $c3 = $ConstT(7);
    my $c4 = $ConstT('7');
    my $app_x_x = $AppT($x, $x);
    my $app_x_y = $AppT($x, $y);
    my $app_y_x = $AppT($y, $x);
    my $lam_x_x = $LamT($x, $x);
    my $lam_y_y = $LamT($y, $y);

    test-eq($x,         $x,             $true );
    test-eq($x,         $VarT('x'),     $true );
    test-eq($x,         $y,             $false);
    test-eq($x,         $app_x_y,       $false);
    test-eq($x,         $app_y_x,       $false);
    test-eq($x,         $c1,            $false);
    test-eq($x,         $c2,            $false);

    test-eq($app_x_y,   $app_x_y,       $true );
    test-eq($app_x_y,   $AppT($x, $y),  $true );    # another instance
    test-eq($app_x_y,   $app_y_x,       $false);
    test-eq($app_x_y,   $c1,            $false);
    test-eq($app_x_y,   $c2,            $false);

    test-eq($lam_x_x,   $lam_x_x,       $true );
    test-eq($lam_x_x,   $LamT($x, $x),  $true );    # another instance
    test-eq($lam_y_y,   $lam_y_y,       $true );
    test-eq($lam_x_x,   $lam_y_y,       $false);    # this is NOT alpha-equivalence!
    test-eq($lam_x_x,   $app_y_x,       $false);
    test-eq($lam_x_x,   $app_x_x,       $false);
    test-eq($lam_x_x,   $x,             $false);
    test-eq($lam_x_x,   $c1,            $false);
    test-eq($lam_x_x,   $c2,            $false);

    #test-eq($c1,        $c1,            $true );   # TODO: compare two ConstT for equality
    #test-eq($c1,        $c2,            $false);
    #test-eq($c1,        $c3,            $false);
    #test-eq($c1,        $c4,            $false);
    #test-eq($c2,        $c2,            $true );
    #test-eq($c2,        $c3,            $false);
    #test-eq($c2,        $c4,            $false);
    #test-eq($c3,        $c3,            $true );
    #test-eq($c3,        $c4,            $false);
    #test-eq($c4,        $c4,            $true );

}


# ->Str -----------------------------------------------------------------------

{ # Term->Str
    is_properLambdaFn($Term2Str);

    is $Term2Str.symbol, 'Term->Str', '$Term2Str.symbol';
    is $Term2Str.Str,    'Term->Str', '$Term2Str.Str';
}


# pattern matching ------------------------------------------------------------

{ # case-Term
    my (&onVarT, &onAppT, &onLamT, &onConstT);
    {
        my &thenFn1 = curry(-> Str $which, $field1 {
            "&$which called: " ~ ($field1.?lambda // $field1.perl);
        });
        my &thenFn2 = curry(-> Str $which, $field1, $field2 {
            "&$which called: " ~ ($field1.?lambda // $field1.perl) ~ ', ' ~ ($field2.?lambda // $field2.perl);
        });
        &onVarT   = &thenFn1('onVarT');
        &onAppT   = &thenFn2('onAppT');
        &onLamT   = &thenFn2('onLamT');
        &onConstT = &thenFn1('onConstT');
    }
    
    my $x = $VarT('x');
    my $y = $VarT('y');
    my $c1 = $ConstT('one');
    my $c2 = $ConstT('two');
    my $app1 = $AppT($y, $x);
    my $app2 = $AppT($x, $y);
    my $lam1 = $LamT($y, $x);
    my $lam2 = $LamT($x, $lam1);
    my $out;


    subtest( {  # when-VarT alone
        sub match(TTerm:D $t) {
            case-Term($t,
                VarT => &onVarT,
                AppT => &onAppT,
                LamT => &onLamT,
                ConstT => &onConstT
            )
        };

        is match($x),       '&onVarT called: "x"', 'match on (VarT x) passes fields to &onVarT';
        is match($y),       '&onVarT called: "y"', 'match on (VarT y) passes fields to &onVarT';
        is match($app1),    '&onAppT called: (VarT "y"), (VarT "x")', 'match on (AppT y x) passes fields to &onAppT';
        is match($app2),    '&onAppT called: (VarT "x"), (VarT "y")', 'match on (AppT x y) passes fields to &onAppT';
        is match($lam1),    '&onLamT called: (VarT "y"), (VarT "x")', 'match on (LamT y x) passes fields to &onLamT';
        is match($lam2),    '&onLamT called: (VarT "x"), (LamT (VarT "y") (VarT "x"))', 'match on (LamT x (LamT y x)) passes fields to &onLamT';
        is match($c1),      '&onConstT called: "one"', 'match on (ConstT "one") passes fields to &onConstT';
        is match($c2),      '&onConstT called: "two"', 'match on (ConstT "two") passes fields to &onConstT';
    });

}



# VarT ------------------------------------------------------------------------

{ # ctor VarT
    is_properLambdaFn($VarT);

    is $VarT.symbol,        'VarT', '$VarT.symbol';
    is $VarT.Str,           'VarT', '$VarT.Str';
    doesnt_ok $VarT, TTerm, 'VarT', :msg('VarT is NOT a TTerm in itself');
    dies_ok { $Term2Str($VarT) }, "($Term2Str $VarT) yields error";
    
    my $x;
    $x = $VarT("foo");
    is $Term2Str($x), '(VarT "foo")',
        "($Term2Str (VarT \"foo\"))";
    does_ok $x, TTerm, "$x";
    is_validLambda $x;
    doesnt_ok $x, Definition;
}

{ # predicate VarT?
    is_properLambdaFn($is-VarT);

    is $is-VarT.symbol,        'VarT?', '$is-VarT.symbol';
    is $is-VarT.Str,           'VarT?', '$is-VarT.Str';
    doesnt_ok $is-VarT, TTerm, 'VarT?', :msg('VarT? is NOT a TTerm in itself');
    dies_ok {$Term2Str($is-VarT) }, "($Term2Str VarT?) yields error";

    my $x;
    $x = $VarT("foo");
    is $is-VarT($x),  $true, "($is-VarT $x)";
    
    my $u = $VarT('u');
    my $v = $VarT('v');
    $x = $AppT($u, $v);
    is $is-VarT($x),  $false, "($is-VarT $x)";
    
    $x = $LamT($u, $v);
    is $is-VarT($x),  $false, "($is-VarT $x)";

    $x = $ConstT("foo");
    is $is-VarT($x),  $false, "($is-VarT $x)";
}

{ # projection VarT->name
    is_properLambdaFn($VarT2name);

    is $VarT2name.symbol,        'VarT->name', '$VarT2name.symbol';
    is $VarT2name.Str,           'VarT->name', '$VarT2name.Str';
    doesnt_ok $VarT2name, TTerm, 'VarT->name', :msg('VarT2name is NOT a TTerm in itself');
    dies_ok {$Term2Str($VarT2name) }, "($Term2Str VarT->name) yields error";
    
    my $x;
    $x = $VarT("foo");
    is $VarT2name($x),  'foo', "($VarT2name $x)";

    my $u = $VarT('u');
    my $v = $VarT('v');
    $x = $AppT($u, $v);
    dies_ok( { $VarT2name($x) }, "($VarT2name $x) yields error");

    $x = $LamT($u, $v);
    dies_ok( { $VarT2name($x) }, "($VarT2name $x) yields error");
}


# AppT ------------------------------------------------------------------------

{ # ctor AppT
    is_properLambdaFn($AppT);

    is $AppT.symbol,        'AppT', '$AppT.symbol';
    is $AppT.Str,           'AppT', '$AppT.Str';
    doesnt_ok $AppT, TTerm, 'AppT', :msg('AppT is NOT a TTerm in itself');
    dies_ok { $Term2Str($AppT) }, "($Term2Str $AppT) yields error";
    
    my $u = $VarT('u');
    my $v = $VarT('v');
    my $x;
    $x = $AppT($u, $v);
    is $Term2Str($x), "(AppT $u $v)",
        "($Term2Str (AppT $u $v)) -> '(AppT $u $v)'";
    does_ok $x, TTerm, "$x";
    is_validLambda $x;
    doesnt_ok $x, Definition;
}

{ # predicate AppT?
    is_properLambdaFn($is-AppT);

    is $is-AppT.symbol,        'AppT?', '$is-AppT.symbol';
    is $is-AppT.Str,           'AppT?', '$is-AppT.Str';
    doesnt_ok $is-AppT, TTerm, 'AppT?', :msg('AppT? is NOT a TTerm in itself');
    dies_ok {$Term2Str($is-AppT) }, "($Term2Str AppT?) yields error";
    
    my $u = $VarT('u');
    my $v = $VarT('v');

    is $is-AppT($u),  $false, "($is-AppT $u)";

    my $x;
    $x = $AppT($u, $v);
    is $is-AppT($x),  $true,  "($is-AppT $x)";
    
    $x = $LamT($u, $v);
    is $is-AppT($x),  $false, "($is-AppT $x)";

    $x = $ConstT("foo");
    is $is-AppT($x),  $false, "($is-AppT $x)";
}

{ # projection AppT->func
    is_properLambdaFn($AppT2func);

    is $AppT2func.symbol,        'AppT->func', '$AppT2func.symbol';
    is $AppT2func.Str,           'AppT->func', '$AppT2func.Str';
    doesnt_ok $AppT2func, TTerm, 'AppT->func', :msg('AppT2func is NOT a TTerm in itself');
    dies_ok {$Term2Str($AppT2func) }, "($Term2Str AppT->func) yields error";
    
    my $x;
    $x = $VarT("foo");
    dies_ok( { $AppT2func($x) }, "($AppT2func $x) yields error");

    my $u = $VarT('u');
    my $v = $VarT('v');
    $x = $AppT($u, $v);
    is $AppT2func($x), $u, "($AppT2func $x)";

    $x = $LamT($u, $v);
    dies_ok( { $AppT2func($x) }, "($AppT2func $x) yields error");
}

{ # projection AppT->arg
    is_properLambdaFn($AppT2arg);

    is $AppT2arg.symbol,        'AppT->arg', '$AppT2arg.symbol';
    is $AppT2arg.Str,           'AppT->arg', '$AppT2arg.Str';
    doesnt_ok $AppT2arg, TTerm, 'AppT->arg', :msg('AppT2arg is NOT a TTerm in itself');
    dies_ok {$Term2Str($AppT2arg) }, "($Term2Str AppT->arg) yields error";
    
    my $x;
    $x = $VarT("foo");
    dies_ok( { $AppT2arg($x) }, "($AppT2arg $x) yields error");

    my $u = $VarT('u');
    my $v = $VarT('v');
    $x = $AppT($u, $v);
    is $AppT2arg($x), $v, "($AppT2arg $x)";

    $x = $LamT($u, $v);
    dies_ok( { $AppT2arg($x) }, "($AppT2arg $x) yields error");
}


# LamT ------------------------------------------------------------------------

{ # ctor LamT
    is_properLambdaFn($LamT);

    is $LamT.symbol,        'LamT', '$LamT.symbol';
    is $LamT.Str,           'LamT', '$LamT.Str';
    doesnt_ok $LamT, TTerm, 'LamT', :msg('LamT is NOT a TTerm in itself');
    dies_ok { $Term2Str($LamT) }, "($Term2Str $LamT) yields error";
    
    my $u = $VarT('u');
    my $v = $VarT('v');
    my $x;
    $x = $LamT($u, $v);
    is $Term2Str($x), "(LamT $u $v)",
        "($Term2Str (LamT $u $v)) -> '(LamT $u $v)'";
    does_ok $x, TTerm, "$x";
    is_validLambda $x;
    doesnt_ok $x, Definition;

    dies_ok({ $LamT($x, $v) }, '$LamT yields an error if 1st arg is not a VarT');
}

{ # predicate LamT?
    is_properLambdaFn($is-LamT);

    is $is-LamT.symbol,        'LamT?', '$is-LamT.symbol';
    is $is-LamT.Str,           'LamT?', '$is-LamT.Str';
    doesnt_ok $is-LamT, TTerm, 'LamT?', :msg('LamT? is NOT a TTerm in itself');
    dies_ok {$Term2Str($is-LamT) }, "($Term2Str LamT?) yields error";
    
    my $u = $VarT('u');
    my $v = $VarT('v');
    my $x;
    $x = $LamT($u, $v);
    is $is-LamT($x),  $true,  "($is-LamT $x)";
    
    $x = $AppT($u, $v);
    is $is-LamT($x),  $false, "($is-LamT $x)";

    is $is-LamT($u),  $false, "($is-LamT $u)";

    $x = $ConstT("foo");
    is $is-LamT($x),  $false, "($is-LamT $x)";
}

{ # projection LamT->var
    is_properLambdaFn($LamT2var);

    is $LamT2var.symbol,        'LamT->var', '$LamT2var.symbol';
    is $LamT2var.Str,           'LamT->var', '$LamT2var.Str';
    doesnt_ok $LamT2var, TTerm, 'LamT->var', :msg('LamT2var is NOT a TTerm in itself');
    dies_ok {$Term2Str($LamT2var) }, "($Term2Str LamT->var) yields error";
    
    my $x;
    $x = $VarT("foo");
    dies_ok( { $LamT2var($x) }, "($LamT2var $x) yields error");

    my $u = $VarT('u');
    my $v = $VarT('v');
    $x = $AppT($u, $v);
    dies_ok( { $LamT2var($x) }, "($LamT2var $x) yields error");

    $x = $LamT($u, $v);
    is $LamT2var($x), $u, "($LamT2var $x)";
}

{ # projection LamT->body
    is_properLambdaFn($LamT2body);

    is $LamT2body.symbol,        'LamT->body', '$LamT2body.symbol';
    is $LamT2body.Str,           'LamT->body', '$LamT2body.Str';
    doesnt_ok $LamT2body, TTerm, 'LamT->body', :msg('LamT2body is NOT a TTerm in itself');
    dies_ok {$Term2Str($LamT2body) }, "($Term2Str LamT->body) yields error";
    
    my $x;
    $x = $VarT("foo");
    dies_ok( { $LamT2body($x) }, "($LamT2body $x) yields error");

    my $u = $VarT('u');
    my $v = $VarT('v');
    $x = $AppT($u, $v);
    dies_ok( { $LamT2body($x) }, "($LamT2body $x) yields error");

    $x = $LamT($u, $v);
    is $LamT2body($x), $v, "($LamT2body $x)";
}


# ConstT ----------------------------------------------------------------------

{ # ctor ConstT
    is_properLambdaFn($VarT);

    is $ConstT.symbol,        'ConstT', '$ConstT.symbol';
    is $ConstT.Str,           'ConstT', '$ConstT.Str';
    doesnt_ok $ConstT, TTerm, 'ConstT', :msg('ConstT is NOT a TTerm in itself');
    dies_ok { $Term2Str($ConstT) }, "($Term2Str $ConstT) yields error";
    
    my $x;
    $x = $ConstT("foo");
    is $Term2Str($x), '(ConstT "foo")',
        "($Term2Str (ConstT \"foo\"))";
    does_ok $x, TTerm, "$x";
    is_validLambda $x;
    doesnt_ok $x, Definition;
}

{ # predicate ConstT?
    is_properLambdaFn($is-ConstT);

    is $is-ConstT.symbol,        'ConstT?', '$is-ConstT.symbol';
    is $is-ConstT.Str,           'ConstT?', '$is-ConstT.Str';
    doesnt_ok $is-ConstT, TTerm, 'ConstT?', :msg('ConstT? is NOT a TTerm in itself');
    dies_ok {$Term2Str($is-ConstT) }, "($Term2Str ConstT?) yields error";

    my $x;
    $x = $VarT("foo");
    is $is-ConstT($x),  $false, "($is-ConstT $x)";
    
    my $u = $VarT('u');
    my $v = $VarT('v');
    $x = $AppT($u, $v);
    is $is-ConstT($x),  $false, "($is-ConstT $x)";
    
    $x = $LamT($u, $v);
    is $is-ConstT($x),  $false, "($is-ConstT $x)";

    $x = $ConstT("foo");
    is $is-ConstT($x),  $true, "($is-ConstT $x)";
}

{ # projection ConstT->value
    is_properLambdaFn($ConstT2value);

    is $ConstT2value.symbol,        'ConstT->value', '$ConstT2value.symbol';
    is $ConstT2value.Str,           'ConstT->value', '$ConstT2value.Str';
    doesnt_ok $ConstT2value, TTerm, 'ConstT->value', :msg('ConstT2value is NOT a TTerm in itself');
    dies_ok {$Term2Str($ConstT2value) }, "($Term2Str ConstT->value) yields error";
    
    my $x;
    $x = $ConstT("foo");
    is $ConstT2value($x),  'foo', "($ConstT2value $x)";

    my $u = $VarT('u');
    dies_ok( { $ConstT2value($u) }, "($ConstT2value $u) yields error");

    my $v = $VarT('v');
    $x = $AppT($u, $v);
    dies_ok( { $ConstT2value($x) }, "($ConstT2value $x) yields error");

    $x = $LamT($u, $v);
    dies_ok( { $ConstT2value($x) }, "($ConstT2value $x) yields error");
}


