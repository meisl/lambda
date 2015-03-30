use v6;
use Test;
use Test::Util;
use Test::Util_Lambda;
use Test::Util_List;
use Test::Util_Term;

use Lambda::Boolean;
use Lambda::MaybeADT;
use Lambda::PairADT;
use Lambda::TermADT;
use Lambda::ListADT;


# module under test:
use Lambda::Substitution;

plan 16;


{ # function (subst forVar whatTerm inTerm)
    is_properLambdaFn $subst, 'subst';

    testTermFn($subst, 
        ['x', `'y'  , `'"c"'   ] => $None,
        ['x', `'"c"', `'x'     ] => $Some(`'"c"'),
        ['y', `'"c"', `'x'     ] => $None,
        ['x', `'y'  , `'x'     ] => $Some(`'y'),
        ['x', `'y'  , `'λx.x y'] => $None,
        ['z', `'y'  , `'λx.x y'] => $None,
        ['y', `'z'  , `'λx.x y'] => $Some(`'λx.x z'),
    );
}


{ # function (subst-seq inTerm substitutions)
    is_properLambdaFn $subst-seq, 'subst-seq';

    testTermFn($subst-seq, 
        [`'"c"',       [y => `'x'        ]]   => $None,
        [`'z',         [y => `'x'        ]]   => $None,
        [`'y',         [y => `'x'        ]]   => $Some(`'x'),
        [`'y',         [y => `'λu.λv.z u']]   => $Some(`'λu.λv.z u'),
        [`'λu.λv.z u', [y => `'x'        ]]   => $None,               # because y doesn't occur in (λu.λv.z u)
        [`'λu.λv.z u', [u => `'x'        ]]   => $None,               # because u is bound
        [`'λu.λv.z u', [z => `'x'        ]]   => $Some(`'λu.λv.x u'), # since z is free in (λu.λv.z u)
        [`'λu.λv.z u', [z => `'u'        ]]   => $Some(`'λu.λv.u u'), # since z is free in (λu.λv.z u) (accidental capture)
        
        [`'z',         [z => `'λw.λx.x z', z => `'y', y => `'λw.λx.x z']  ] => $Some(`'λw.λx.x (λw.λx.x z)'),
            # [λw.λx.x z/y]([y/z]([λw.λx.x z/z]z))
        
        [`'λu.λv.z u', [z => `'x',         x => `'y']                     ] => $Some(`'λu.λv.y u'),
            # [y/x]([x/z]λu.λv.z u)                 -> λu.λv.y u
        
        [`'λu.λv.z u', [z => `'x',         y => `'z', x => `'y']          ] => $Some(`'λu.λv.y u'),  # 2nd subst doesn't change anything
            # [y/x]([z/y]([x/z]λu.λv.z u))          -> λu.λv.y u
        
        [`'λu.λv.z u', [z => `'λw.λx.x z', z => `'y']                     ] => $Some(`'λu.λv.(λw.λx.x y) u'),
            # [y/z]([λw.λx.x z/z]λu.λv.z u)         -> λu.λv.(λw.λx.x y) u
    );
}


{ # subst-par-alpha
    my sub test_variant_subst-par-alpha($fut) {
        testTermFn($fut,
            [[x => `'y'],   `'"c"' ] => $None,

            [[x => `'y'],   `'y'   ] => $None,
            [[x => `'y'],   `'x'   ] => $Some(`'y'),

            [[x => `'y'],   `'x x' ] => $Some(`'y y'),

            [[z => `'y'],   `'x y' ] => $None,
            [[x => `'y'],   `'x y' ] => $Some(`'y y'),
            [[y => `'x'],   `'x y' ] => $Some(`'x x'),
                      
            [[x => `'y'],   `'λx.y'] => $None,
            [[z => `'y'],   `'λx.y'] => $None,
            [[y => `'z'],   `'λx.y'] => $Some(`'λx.z'),

            # main subst var x NOT free in body:
            [[x => `'z'],   `'λx.x y' ] => $None,
            
            # main subst var y IS free in body:
            [[y => `'z'],   `'λx.x y' ] => $Some(`'λx.x z'),  # ...*except* for the lambda's binder!

            # neither forVar nor var free in body, and no external alpha-convs applicable
            [[v => `'x y'], `'λu.x y z'] => $None,
        );

        subtest({ # [(x y)/y](λx.x y z)  =  (λα1.α1 (x y) z)
            my ($out, $α1, $t);
            
            $out = $fut($cons($Pair('y', `'x y'), $nil), `'λx.x y z');
            diag lambdaArgToStr($out);
            $t = $Some2value($out);

            $α1 = $LamT2var($t);
            isnt_in($α1, <x y z>, "fresh var $α1 is different from x, y and z");
            
            is_eq-Term($t, $LamT($α1, $AppT($AppT($VarT($α1), `'x y'), `'z')), 
                '[(x y)/y](λx.x y z)  =  (λα1.α1 (x y) z)');
        }, 'plus additional alpha-conversion (fresh var for x)');

        subtest({ # [(x y)/y](λz.λx.x y z)  =  (λz.λα1.α1 (x y) z)
            my ($out, $α1, $t);
            
            $out = $fut($cons($Pair('y', `'x y'), $nil), `'λz.λx.x y z');
            diag lambdaArgToStr($out);
            $t = $Some2value($out);

            $α1 = $LamT2var($LamT2body($t));
            isnt_in($α1, <x y z>, "fresh var $α1 is different from x, y and z");
            
            is_eq-Term($t, $LamT('z', $LamT($α1, $AppT($AppT($VarT($α1), `'x y'), `'z'))), 
                '[(x y)/y](λz.λx.x y z)  =  (λz.λα1.α1 (x y) z)');
        }, 'plus additional alpha-conversion (fresh var for x) under binder z');
        
        subtest({ # [(x y)/z](λy.λx.x y z)  =  (λα1.λα2.α2 α1 (x y))
            my ($out, $α1, $α2, $t);
            
            $out = $fut($cons($Pair('z', `'x y'), $nil), `'λy.λx.x y z');
            diag lambdaArgToStr($out);
            $t = $Some2value($out);

            $α1 = $LamT2var($t);
            $α2 = $LamT2var($LamT2body($t));

            isnt_in($α1, <x y z>, "fresh var $α1 is different from x, y and z");
            isnt_in($α2, <x y z>, "fresh var $α2 is different from x, y and z");
            
            is_eq-Term($t, $LamT($α1, $LamT($α2, $AppT($AppT($VarT($α2), $VarT($α1)), `'x y'))), 
                '[(x y)/z](λy.λx.x y z)  =  (λα1.λα2.α2 α1 (x y))');
        }, 'plus additional alpha-conversions (fresh var for x and y)');
        
        subtest({ # [(x y)/z](λy.λx.x y z ((λz.λx.x y z) (λx.y x)))  =  (λα1.λα2.α2 α1 (x y) ((λz.λx.x α1 z) (λx.α1 x)))
            my ($out, $α1, $α2, $t);
            
            $out = $fut($cons($Pair('z', `'x y'), $nil), `'λy.λx.x y z ((λz.λx.x y z) (λx.y x))');
            diag lambdaArgToStr($out);
            $t = $Some2value($out);

            $α1 = $LamT2var($t);
            $α2 = $LamT2var($LamT2body($t));

            isnt_in($α1, <x y z>, "fresh var $α1 is different from x, y and z");
            isnt_in($α2, <x y z>, "fresh var $α2 is different from x, y and z");

            my $λx_α1x = $LamT('x', $AppT($VarT($α1), `'x'));
            my $λz_λx_xα1z = $LamT('z', $LamT('x', $AppT($AppT(`'x', $VarT($α1)), `'z')));
            my $α2α1_xy = $AppT($AppT($VarT($α2), $VarT($α1)), `'(x y)');

            is_eq-Term($t, $LamT($α1, $LamT($α2, $AppT($α2α1_xy, $AppT($λz_λx_xα1z, $λx_α1x)))),
                '[(x y)/z](λy.λx.x y z ((λz.λx.x y z) (λx.y x)))  =  (λα1.λα2.α2 α1 (x y) ((λz.λx.x α1 z) (λx.α1 x)))');
        }, 'plus additional alpha-conversions (fresh var for x and y, but omitting unnecessary alpha-conversions)');
    }

    is_properLambdaFn $subst-par-alpha, 'subst-par-alpha';
    test_variant_subst-par-alpha($subst-par-alpha);

    is_properLambdaFn $subst-par-alpha_direct, 'subst-par-alpha_direct';
    test_variant_subst-par-alpha(
        -> TList $substitutions, TTerm $t {
            my $out = $subst-par-alpha_direct($substitutions, $t);
            _if_($Term-eq($out, $t),
                $None,
                { $Some($out) }
            )
        }
    );

}

