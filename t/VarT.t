use v6;
use Test;
use Test::Util;
use Test::Util_Lambda;


# module under test (the VarT part only):
use Lambda::TermADT;

plan 28;


{ # (VarT Str) [fka VarT.get]
    my $x1 = $VarT('x');
    my $x2 = $VarT('x');

    cmp_ok($x1, '===', $x2, '(VarT Str) returns same var for same name');
    
    my $y1 = $VarT('y');
    isnt($y1, $x1, '(VarT Str) returns new instance if necessary');
    is($VarT2name($y1), 'y', '(VarT Str) returns new instance if necessary');
    my $y2 = $VarT('y');
    cmp_ok($y1, '===', $y2, '(VarT Str) returns same var for same name');
}

{ # fresh-var-for
    is_properLambdaFn($fresh-var-for);

    is $fresh-var-for.symbol, 'fresh-var-for', '$fresh-var-for.symbol';
    is $fresh-var-for.Str,    'fresh-var-for', '$fresh-var-for.Str';

    my $x   = $VarT('x');
    my $y   = $VarT('y');
    my $app = $AppT($x, $y);
    my $lam = $LamT($x, $x);
    my $c   = $ConstT(23);

    dies_ok( { $fresh-var-for($app) }, '$fresh-var-for does not accept an AppT arg');
    dies_ok( { $fresh-var-for($lam) }, '$fresh-var-for does not accept an LamT arg');
    dies_ok( { $fresh-var-for($c  ) }, '$fresh-var-for does not accept an ConstT arg');

    my $fresh1 = $fresh-var-for($x);
    my $fresh2 = $fresh-var-for($x);

    isnt($VarT2name($fresh1), $VarT2name($x), "fresh var has name different from any other");
    isnt($VarT2name($fresh1), $VarT2name($y), "fresh var has name different from any other");
    isnt($VarT2name($fresh1), $VarT2name($fresh2), "fresh var has name different from any other");

    my $fresh3 = $fresh-var-for($x);

    isnt($VarT2name($fresh3), $VarT2name($x), "fresh var has name different from any other");
    isnt($VarT2name($fresh3), $VarT2name($y), "fresh var has name different from any other");
    isnt($VarT2name($fresh3), $VarT2name($fresh1), "fresh var has name different from any other");
    isnt($VarT2name($fresh3), $VarT2name($fresh2), "fresh var has name different from any other");

    my $xname = $VarT2name($x);
    ok($fresh3.gist ~~ / '/' $xname /, ".fresh(:for).gist contains the given var's gist")
        or diag "# got: {$fresh3.gist}";
    nok($VarT2name($fresh3) ~~ / $xname /, ".fresh(:for).name does NOT contain the given var's name");
    cmp_ok $fresh3, '===', $VarT($VarT2name($fresh3)), "can get back same instance of fresh var via VarT.get";

    my $fresh4 = $fresh-var-for($fresh3);

    isnt($VarT2name($fresh4), $VarT2name($x), "fresh var has name different from any other");
    isnt($VarT2name($fresh4), $VarT2name($y), "fresh var has name different from any other");
    isnt($VarT2name($fresh4), $VarT2name($fresh1), "fresh var has name different from any other");
    isnt($VarT2name($fresh4), $VarT2name($fresh2), "fresh var has name different from any other");
    isnt($VarT2name($fresh4), $VarT2name($fresh3), "fresh var has name different from any other");

    my $f3name = $VarT2name($fresh3);
    ok($fresh4.gist ~~ / $f3name /, ".fresh(:for).gist contains the given var's gist")
        or diag "# got: {$fresh4.gist}";
    nok($VarT2name($fresh4) ~~ / $f3name /, ".fresh(:for).name does NOT contain the given var's name");
    cmp_ok $fresh3, '===', $VarT($VarT2name($fresh3)), "can get back same instance of fresh var via VarT.get";
}
