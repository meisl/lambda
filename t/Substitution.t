use v6;

use Test;
use Lambda::LambdaModel;

plan *;

{ # Term.subst($what, :for)
    my $x = VarT.new(:name<x>);
    my $y = VarT.new(:name<y>);

    my $c = ConstT.new(:value('c'));

    my $s = $c.subst($y, :for($x));
    is($c, $s, 'substituting in a ConstT returns just the ConstT');

    #$x.substitute($c, :for($x));
}