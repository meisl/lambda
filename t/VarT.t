use v6;

use Test;
use Lambda::LambdaModel;

plan *;

{
    my $x = VarT.new(:name<x>);
    my $fresh1 = VarT.fresh;
    my $fresh2 = VarT.fresh;
    my $y = VarT.new(:name<y>);

    isnt($fresh1.name, $x.name, "fresh var has name different from any other");
    isnt($fresh1.name, $y.name, "fresh var has name different from any other");
    isnt($fresh1.name, $fresh2.name, "fresh var has name different from any other");

    my $fresh3 = VarT.fresh(:for($x));

    isnt($fresh3.name, $x.name, "fresh var has name different from any other");
    isnt($fresh3.name, $y.name, "fresh var has name different from any other");
    isnt($fresh3.name, $fresh1.name, "fresh var has name different from any other");
    isnt($fresh3.name, $fresh2.name, "fresh var has name different from any other");

    my $xname = $x.name;
    ok($fresh3.gist ~~ / '/' $xname /, ".fresh(:for).gist contains the given var's gist");
    nok($fresh3.name ~~ / $xname /, ".fresh(:for).name does NOT contain the given var's name");

    my $fresh4 = VarT.fresh(:for($fresh3));

    isnt($fresh4.name, $x.name, "fresh var has name different from any other");
    isnt($fresh4.name, $y.name, "fresh var has name different from any other");
    isnt($fresh4.name, $fresh1.name, "fresh var has name different from any other");
    isnt($fresh4.name, $fresh2.name, "fresh var has name different from any other");
    isnt($fresh4.name, $fresh3.name, "fresh var has name different from any other");

    my $f3name = $fresh3.name;
    ok($fresh4.gist ~~ / $f3name /, ".fresh(:for).gist contains the given var's gist");
    nok($fresh4.name ~~ / $f3name /, ".fresh(:for).name does NOT contain the given var's name");
}