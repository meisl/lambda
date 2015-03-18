use v6;
use Test;
use Test::Util;
use Test::Util_Lambda;

use Lambda::Boolean;
use Lambda::MaybeADT;
use Lambda::ListADT;
use Lambda::PairADT;
use Lambda::TermADT;

use Lambda::Conversion::Bool-conv;
use Lambda::Conversion::ListADT-conv;


# module under test:
use Lambda::Substitution;

plan 35;


my $a = $VarT('a');
my $u = $VarT('u');
my $v = $VarT('v');
my $w = $VarT('w');
my $x = $VarT('x');
my $y = $VarT('y');
my $z = $VarT('z');
my $c = $ConstT('c');

my $app_xx  = $AppT($x, $x);        # (x x)
my $app_xy  = $AppT($x, $y);        # (x y)
my $app_xyz = $AppT($app_xy, $z);   # ((x y) z)
my $lam0    = $LamT('x', $y);        # λx.y
my $lam1    = $LamT('x', $app_xy);   # λx.x y
my $lam2    = $LamT('x', $app_xyz);  # λx.x y z
my $lam3    = $LamT('u', $app_xyz);  # λu.x y z


{ # function (subst inTerm whatTerm forVar)
    is_properLambdaFn $subst, 'subst';

    my sub is_subst(*@tests) {
        for @tests -> $test {
            my $inTerm      = $test.key[0];
            my $inTermStr   = $Term2source($inTerm);

            my $forVarName    = $test.key[1].key;
            my $forVarNameStr = $forVarName.perl;
            my $whatTerm      = $test.key[1].value;
            my $whatTermStr   = $Term2source($whatTerm);

            my $expected      = $test.value;
            my $itself        = $expected === $None;
            my $expStr        = $itself
                                 ?? "the original term"
                                 !! '(Some `' ~ $Term2source($Some2value($expected)) ~ ')';
            my $desc = "substituting $whatTermStr for $forVarNameStr in $inTermStr yields $expStr";

            my $actual = $subst($inTerm, $whatTerm, $forVarName);
            is($actual, $expected, $desc)
                or diag($actual.perl) and die;
        }
    }

    is_subst(
        [$c,                        x => $y] => $None,
        [$x,                        x => $c] => $Some($c),
        [$x,                        y => $c] => $None,
        [$x,                        x => $y] => $Some($y),
        [$LamT('x', $AppT($x, $y)),  x => $y] => $None,                              # y for x in (λx.x y) -> (λx.x y)
        [$LamT('x', $AppT($x, $y)),  z => $y] => $None,                              # y for z in (λx.x y) -> (λx.x y)
        [$LamT('x', $AppT($x, $y)),  y => $z] => $Some($LamT('x', $AppT($x, $z))),    # z for y in (λx.x y) -> (λx.x z)
    );
}

{ # function (subst-seq inTerm substitutions)
    is_properLambdaFn $subst-seq, 'subst-seq';

    my sub is_subst-seq(*@tests) {
        for @tests -> $test {
            my $inTerm      = $test.key[0];
            my $inTermStr   = $Term2source($inTerm);

            my $substs      = $test.key[1];
            my $substsStr   = '[' ~ $substs.map(-> $pair { "[{$Term2source($pair[1])}/{$pair[0]}]"}).join(', ') ~ ']';
            my $substsListOfPairs = convertP6ArrayToTListOfTPairs($substs);

            my $expected   = $test.value;
            my $itself     = $expected === $None;
            my $expStr     = $itself
                                 ?? "the original term"
                                 !! '(Some `' ~ $Term2source($Some2value($expected)) ~ ')';
            my $desc = "applying substitutions $substsStr in $inTermStr yields $expStr";

            my $actual = $subst-seq($inTerm, $substsListOfPairs);
            is($actual, $expected, $desc)
                or diag($actual.Str ~ ' / ' ~ $actual.perl) and die;
        }
    }

    my $l1 = $LamT('u', $LamT('v', $AppT($z, $u)));   # λu.λv.z u
    my $l2 = $LamT('w', $LamT('x', $AppT($x, $z)));   # λw.λx.x z
    my $l3 = $LamT('u', $LamT('v', $AppT($x, $u)));   # λu.λv.x u
    my $l4 = $LamT('u', $LamT('v', $AppT($u, $u)));   # λu.λv.u u
    my $l5 = $LamT('w', $LamT('x', $AppT($x, $l2)));   # λw.λx.x λw.λx.x z
    my $l6 = $LamT('u', $LamT('v', $AppT($y, $u)));   # λu.λv.y u
    my $l7 = $LamT('u', $LamT('v', $AppT($LamT('w', $LamT('x', $AppT($x, $y))), $u)));   # λu.λv.(λw.λx.x y) u

    is_subst-seq(
        [$c,  [['y', $x]]]   => $None,       # [x/y]"c"          -> "c"
        [$z,  [['y', $x]]]   => $None,       # [x/y]z            -> z
        [$y,  [['y', $x]]]   => $Some($x),   # [x/y]y            -> x
        [$y,  [['y', $l1]]]  => $Some($l1),  # [λu.λv.z u/y]y    -> λu.λv.z u
        [$l1, [['y', $x]]]   => $None,       # [x/y]λu.λv.z u    -> λu.λv.z u    # because y doesn't occur in l1
        [$l1, [['u', $x]]]   => $None,       # [x/u]λu.λv.z u    -> λu.λv.z u    # because u is bound
        [$l1, [['z', $x]]]   => $Some($l3),  # [x/z]λu.λv.z u    -> λu.λv.x u    # since z is free in l1
        [$l1, [['z', $u]]]   => $Some($l4),  # [u/z]λu.λv.z u    -> λu.λv.u u    # since z is free in l1 (accidental capture)
        
        [$z,  [['z', $l2], ['z', $y], ['y', $l2]]]     => $Some($l5),  
            # [λw.λx.x z/y]([y/z]([λw.λx.x z/z]z))  -> λw.λx.x λw.λx.x z
        [$l1, [['z', $x], ['x', $y]]]                 => $Some($l6),
            # [y/x]([x/z]λu.λv.z u)                 -> λu.λv.y u
        [$l1, [['z', $x], ['y', $z], ['x', $y]]]       => $Some($l6),
            # [y/x]([z/y]([x/z]λu.λv.z u))          -> λu.λv.y u        # 2nd subst doesn't change anything
        [$l1, [['z', $l2], ['z', $y]]]                => $Some($l7),
            # [y/z]([λw.λx.x z/z]λu.λv.z u)         -> λu.λv.(λw.λx.x y) u
    );
}

{ # function (subst-with-alpha forVar whatTerm keepfree alpha-convs inTerm)
    is_properLambdaFn $subst-with-alpha, 'subst-with-alpha';

    my sub is_subst-with-alpha(*@tests) {
        for @tests -> $test {
            my $forVar      = $test.key[0];
            my $forVarStr   = $Term2source($forVar);

            my $whatTerm    = $test.key[1];
            my $whatTermStr = $Term2source($whatTerm);

            my $keepfree    = $test.key[2];
            my $keepfreeStr = '[' ~ $keepfree.map($VarT2name).join(', ') ~ ']';
            my $keepfreeTList = convertP6Array2TList($keepfree);

            my $inTerm      = $test.key[3];
            my $inTermStr   = $Term2source($inTerm);

            my $expected   = $test.value;
            my $itself     = $expected === $None;
            my $expStr     = $itself
                                 ?? "the original term"
                                 !! '(Some `' ~ $Term2source($Some2value($expected)) ~ ')';
            my $desc = "(subst-with-alpha $forVarStr $whatTermStr $keepfreeStr $inTermStr) yields $expStr";

            my $actual = $subst-with-alpha($forVar, $whatTerm, $keepfreeTList, $inTerm);
            my $actualStr = convertTBool2P6Bool($is-Some($actual))
                ?? '(Some `' ~ $Term2source($Some2value($actual)) ~ ')'
                !! 'None';
            is($actual, $expected, $desc)
                or diag("     got: $actualStr  /  {$actual.perl})") and die;
        }
    }

    is_subst-with-alpha(
        [$x, $y,        [$y],         $c      ] => $None,

        [$x, $y,        [$y],         $y      ] => $None,
        [$x, $y,        [$y],         $x      ] => $Some($y),

        [$x, $y,        [$y],         $app_xx ] => $Some($AppT($y, $y)),

        [$z, $y,        [$y],         $app_xy ] => $None,
        [$x, $y,        [$y],         $app_xy ] => $Some($AppT($y, $y)),
        [$y, $x,        [$x],         $app_xy ] => $Some($AppT($x, $x)),
                           
        [$z, $y,        [$y],         $lam0   ] => $None,     # λx.y
        [$y, $z,        [$z],         $lam0   ] => $Some($LamT('x', $z)),

        # main subst var x NOT free in body:     # λx.x y
        [$x, $z,        [$z],         $lam1   ] => $None,
        
        # main subst var y IS free in body:     # λx.x y
        [$y, $z,        [$z],         $lam1   ] => $Some($LamT('x', $AppT($x,$z))),  # ...*except* for the lambda's binder!

        # neither forVar nor var free in body, and no external alpha-convs applicable
        [$v, $app_xy,   [$x, $y],     $lam3   ] => $None,
    );
    
    subtest({ # [(x y)/y](λx.x y z)  =  (λα1.α1 (x y) z)
        my ($out, $newVarName, $newVar, $newBody, $keepfree);
        $keepfree = $cons($x, $cons($y, $nil));
        
        $out = $Some2value($subst-with-alpha($y, $app_xy, $keepfree, $lam2));
        
        $newVarName = $LamT2var($out);    # DONE: LamT_ctor_with_Str_binder
        $newVar     = $VarT($newVarName);
        $newBody    = $LamT2body($out);

        isnt($newVarName, 'x', "fresh var $newVar is different from var x");
        isnt($newVarName, 'y', "fresh var $newVar is different from var y");
        isnt($newVarName, 'z', "fresh var $newVar is different from var z");
        
        is($newBody, $AppT($AppT($newVar, $app_xy), $z))
            or diag("     got: " ~ $Term2source($out));
        # (λx.((x y) z))
        # should have been turned into
        # (λα1.((α1 (x y)) z))

    }, 'plus additional alpha-conversion (fresh var for x)');
}