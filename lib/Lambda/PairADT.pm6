use v6;

use Lambda::Base;
use Lambda::BaseP6;
use Lambda::Boolean;

module Lambda::PairADT;
# data Pair = Pair fst:_ snd:_
role TPair is export {
}


# constructors

constant $Pair is export = lambdaFn(
    'Pair', 'λx.λy.λprj.prj x y',
    -> $x, $y {
        lambdaFn(
            Str, { 'Pair ' ~ ($x.?symbol // $x.?lambda // $x.perl) ~ ' ' ~ ($y.?symbol // $y.?lambda // $y.perl) },
            -> &prj { &prj($x, $y) }
        ) does TPair
    }
);


# no predicates since there's only one constructor


# projections

constant $Pair2fst is export = lambdaFn(
    'Pair->fst', 'λp.p π2->1',
    -> TPair:D $p {
        $p($pi1o2);
    }
);
constant $fst is export := $Pair2fst;


constant $Pair2snd is export = lambdaFn(
    'Pair->snd', 'λp.p π2->2',
    -> TPair:D $p {
        $p($pi2o2);
    }
);
constant $snd is export := $Pair2snd;


# ->Str

constant $Pair2Str is export = lambdaFn(
    'Pair->Str', 'λp.(~ (~ (~ "(Pair " (->str (fst m))) (->str (snd m))) ")")',
    -> TPair:D $p {
        my $x = $fst($p);
        my $y = $snd($p);
        my $xStr = $x.?symbol // $x.?lambda // $x.perl;
        my $yStr = $y.?symbol // $y.?lambda // $y.perl;
        "(Pair $xStr $yStr)";
    }
);
