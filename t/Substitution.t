use v6;

use Test;
use Test::Util;

use Lambda::Boolean;
use Lambda::MaybeADT;
use Lambda::ListADT;
use Lambda::TermADT;

use Lambda::Substitution;

use Lambda::Conversion::Bool-conv;
use Lambda::_Substitution;
use Lambda::LambdaGrammar;
use Lambda::LambdaModel;


plan 15;


my $a = VarT.new(:name('a'));
my $x = VarT.new(:name('x'));
my $y = VarT.new(:name('y'));
my $z = VarT.new(:name('z'));
my $c = ConstT.new(:value('c'));


{ # function (subst inTerm whatTerm forVar)
    is_properLambdaFn $subst;

    is $subst.symbol, 'subst', '$subst.symbol';
    is $subst.Str,    'subst', '$subst.Str';

    my sub is_subst(*@tests) {
        for @tests -> $test {
            my $inTerm      = $test.key[0];
            my $inTermStr   = $Term2source($inTerm);

            my $forVar      = $test.key[1].key;
            my $forVarStr   = $Term2source($forVar);
            my $whatTerm    = $test.key[1].value;
            my $whatTermStr = $Term2source($whatTerm);

            my $expected   = $test.value;
            my $itself     = $expected === $None;
            my $expStr     = $itself
                                 ?? "the original term"
                                 !! '(Some ' ~ $Term2source($Some2value($expected)) ~ ')';
            my $desc = "substituting $whatTermStr for $forVarStr in $inTermStr yields $expStr";

            subtest({
                my $actual = $subst($inTerm, $whatTerm, $forVar);
                is($actual, $expected, $desc)
                    or diag($actual.perl) and die;
                
                my $inTermP6    = convertToP6Term($inTerm);
                my $whatTermP6  = convertToP6Term($whatTerm);
                my $forVarP6    = convertToP6Term($forVar);

                my $expectedP6 = $itself
                    ?? $inTermP6
                    !! convertToP6Term($Some2value($expected));

                is($inTermP6.subst($whatTermP6, :for($forVarP6)), $expectedP6, $desc);
            }, $desc);
        }
    }

    is_subst(
        [$c,                        $x => $y] => $None,
        [$x,                        $x => $c] => $Some($c),
        [$x,                        $y => $c] => $None,
        [$x,                        $x => $y] => $Some($y),
        [$LamT($x, $AppT($x, $y)),  $x => $y] => $None,                              # y for x in (λx.x y) -> (λx.x y)
        [$LamT($x, $AppT($x, $y)),  $z => $y] => $None,                              # y for z in (λx.x y) -> (λx.x y)
        [$LamT($x, $AppT($x, $y)),  $y => $z] => $Some($LamT($x, $AppT($x, $z))),    # z for y in (λx.x y) -> (λx.x z)
    );
}

{ # function (subst-seq inTerm substitutions)
    is_properLambdaFn $subst-seq;

    is $subst-seq.symbol, 'subst-seq', '$subst-seq.symbol';
    is $subst-seq.Str,    'subst-seq', '$subst-seq.Str';

}

{ # Term.subst-seq(@substitutions)
    my $l1 = parseLambda('λa.λb.z a');
    my $l2 = parseLambda('λc.λd.d z');

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
