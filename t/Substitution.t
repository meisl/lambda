use v6;

use Test;
use Test::Util;
use Lambda::LambdaGrammar;
use Lambda::LambdaModel;

use Lambda::Substitution;


plan 11;

{
    is_properLambdaFn $subst;
    is_properLambdaFn $subst-seq;
}

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

{ # Term.subst-seq(@substitutions)
    my $a = parseLambda('a');
    my $x = parseLambda('x');
    my $y = parseLambda('y');
    my $z = parseLambda('z');
    
    my $l1 = parseLambda('λa.λb.z a');
    my $l2 = parseLambda('λc.λd.d z');

    my $c = ConstT.new(:value('c'));
    my $s;
    my $t;
    my $ss;
    
    subtest({
        $s = $c.subst-seq([[$y, $x]]);
        is($s, $c, 'in a ConstT yields just the ConstT');

        $s = $z.subst-seq([[$y, $x]]);
        is($s, $z, 'in a non-matching VarT yields just the VarT');

        $s = $y.subst-seq([[$y, $x]]);
        is($s, $x, 'in a matching VarT yields the replacement term (VarT)');

        $s = $y.subst-seq([[$y, $l1]]);
        is($s, $l1, 'in a matching VarT yields the replacement term (LamT)');

        $s = $l1.subst-seq([[$y, $x]]);
        is($s, $l1, 'in a LamT without any occurrance of the for-VarT yields just the LamT');

        $s = $l1.subst-seq([[$a, $x]]);
        is($s, $l1, 'in a LamT with only a bound occurrance of the for-VarT yields just the LamT');

        $s = $l1.subst-seq([[$z, $x]]);
        is($s, parseLambda('λa.λb.x a'), 'in a LamT with free occurrance of the for-VarT yields changed LamT');

        $s = $l1.subst-seq([[$z, $a]]);
        is($s, parseLambda('λa.λb.a a'), 'in a LamT with free occurrance of the for-VarT yields changed LamT (accidental capture)');
    }, 'subst-seq single subst ');
    
    subtest({
        $s = $z.subst-seq([[$z, $l2], [$z, $y], [$y, $l2]]);
        is($s, parseLambda('λc.λd.d λc.λd.d z'), 
            'in a matching VarT yields rest of substs applied to replacement Term (transitive/Term)');

        $s = $l1.subst-seq([[$z, $x], [$x, $y]]);
        is($s, parseLambda('λa.λb.y a'), 'in a LamT with free occurrance of the for-VarT yields changed LamT (transitive/VarT)');

        $s = $l1.subst-seq([[$z, $x], [$y, $z], [$x, $y]]);
        is($s, parseLambda('λa.λb.y a'), 
            'in a LamT with free occurrance of the for-VarT yields changed LamT (transitive, ignoring inapplicable)');

        $s = $l1.subst-seq([[$z, $l2], [$z, $y]]);
        is($s, parseLambda('λa.λb.(λc.λd.d y) a'), 'in a LamT with free occurrance of the for-VarT yields changed LamT (transitive/Term)');

    }, 'subst-seq two substs ');
}
