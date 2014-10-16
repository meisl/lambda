use v6;

use Test;
use Lambda::LambdaModel;

plan *;

{ # Term.subst($what, :for)
    my $x = VarT.new(:name<x>);
    my $y = VarT.new(:name<y>);

    my $c = ConstT.new(:value('c'));
    my $s;
    
    $s = $c.subst($y, :for($x));
    is($s, $c, 'substituting in a ConstT yields just the ConstT');

    $s = $x.subst($c, :for($x));
    is($s, $c, 'substituting a ConstT in a VarT for that VarT yields the ConstT');

    $s = $x.subst($c, :for($y));
    is($s, $x, 'substituting a ConstT in a VarT for another VarT yields the original VarT');

    $s = $x.subst($y, :for($x));
    is($s, $y, 'substituting a VarT in another VarT for that VarT yields that VarT');
}