use v6;

use Test;
use Lambda::LambdaGrammar;
use Lambda::LambdaModel;

plan 7;

{ # Term.subst($what, :for)
    my $x = parseLambda('x');
    my $y = parseLambda('y');
    my $z = parseLambda('z');

    my $c = ConstT.new(:value('c'));
    my $s;
    my $t;
    
    $s = $c.subst($y, :for($x));
    is($s, $c, 'substituting in a ConstT yields just the ConstT');

    $s = $x.subst($c, :for($x));
    is($s, $c, 'substituting a ConstT in a VarT for that VarT yields the ConstT');

    $s = $x.subst($c, :for($y));
    is($s, $x, 'substituting a ConstT in a VarT for another VarT yields the original VarT');

    $s = $x.subst($y, :for($x));
    is($s, $y, 'substituting a VarT in another VarT for that VarT yields that VarT');

    $t = parseLambda('λx.x y');
    
    $s = $t.subst($y, :for($x));
    is($s, $t, 'substituting in a LamT for a bound VarT doesnt change anything');
    
    $s = $t.subst($y, :for($z));
    is($s, $t, 'substituting in a LamT for a VarT that doesnt occur doesnt change anything');
    
    $s = $t.subst($z, :for($y));
    is($s, parseLambda('λx.x z'), 'substituting in a LamT for an unbound VarT');
}