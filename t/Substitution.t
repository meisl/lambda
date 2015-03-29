use v6;
use Test;
use Test::Util;
use Test::Util_Lambda;
use Test::Util_List;
use Test::Util_Term;

use Lambda::MaybeADT;
use Lambda::PairADT;
use Lambda::TermADT;
use Lambda::ListADT;


# module under test:
use Lambda::Substitution;

plan 10;


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


{ # function (subst-with-alpha forVarName whatTerm keepfreeNames alpha-convs inTerm)
    is_properLambdaFn $subst-with-alpha, 'subst-with-alpha';

    testTermFn($subst-with-alpha,
        ['x', `'y',    ['y'],      `'"c"' ] => $None,

        ['x', `'y',    ['y'],      `'y'   ] => $None,
        ['x', `'y',    ['y'],      `'x'   ] => $Some(`'y'),

        ['x', `'y',    ['y'],      `'x x' ] => $Some(`'y y'),

        ['z', `'y',    ['y'],      `'x y' ] => $None,
        ['x', `'y',    ['y'],      `'x y' ] => $Some(`'y y'),
        ['y', `'x',    ['x'],      `'x y' ] => $Some(`'x x'),
                          
        ['z', `'y',    ['y'],      `'λx.y'] => $None,
        ['y', `'z',    ['z'],      `'λx.y'] => $Some(`'λx.z'),

        # main subst var x NOT free in body:
        ['x', `'z',    ['z'],      `'λx.x y' ] => $None,
        
        # main subst var y IS free in body:
        ['y', `'z',    ['z'],      `'λx.x y' ] => $Some(`'λx.x z'),  # ...*except* for the lambda's binder!

        # neither forVar nor var free in body, and no external alpha-convs applicable
        ['v', `'x y',  ['x', 'y'], `'λu.x y z'] => $None,
    );
    
    subtest({ # [(x y)/y](λx.x y z)  =  (λα1.α1 (x y) z)
        my ($out, $newVarName, $t, $keepfree);
        $keepfree = $cons('x', $cons('y', $nil));
        
        $out = $subst-with-alpha('y', `'x y', $keepfree, `'λx.x y z');
        diag lambdaArgToStr($out);
        $t = $Some2value($out);

        $newVarName = $LamT2var($t);

        isnt($newVarName, 'x', "fresh var $newVarName is different from var x");
        isnt($newVarName, 'y', "fresh var $newVarName is different from var y");
        isnt($newVarName, 'z', "fresh var $newVarName is different from var z");
        
        is_eq-Term($t, $LamT($newVarName, $AppT($AppT($VarT($newVarName), `'x y'), `'z')), 
            '[(x y)/y](λx.x y z)  =  (λα1.α1 (x y) z)');
    }, 'plus additional alpha-conversion (fresh var for x)');
    
    subtest({ # [(x y)/y](λz.λx.x y z)  =  (λz.λα1.α1 (x y) z)
        my ($out, $newVarName, $t, $keepfree);
        $keepfree = $cons('x', $cons('y', $nil));
        
        $out = $subst-with-alpha('y', `'x y', $keepfree, `'λz.λx.x y z');
        diag lambdaArgToStr($out);
        $t = $Some2value($out);

        $newVarName = $LamT2var($LamT2body($t));

        isnt($newVarName, 'x', "fresh var $newVarName is different from var x");
        isnt($newVarName, 'y', "fresh var $newVarName is different from var y");
        isnt($newVarName, 'z', "fresh var $newVarName is different from var z");
        
        is_eq-Term($t, $LamT('z', $LamT($newVarName, $AppT($AppT($VarT($newVarName), `'x y'), `'z'))), 
            '[(x y)/y](λz.λx.x y z)  =  (λz.λα1.α1 (x y) z)');
    }, 'plus additional alpha-conversion (fresh var for x) under binder z');
    
    subtest({ # [(x y)/z](λy.λx.x y z)  =  (λα1.λα2.α2 α1 (x y))
        my ($out, $newVarName1, $newVarName2, $t, $keepfree);
        $keepfree = $cons('x', $cons('y', $nil));
        
        $out = $subst-with-alpha('z', `'x y', $keepfree, `'λy.λx.x y z');
        diag lambdaArgToStr($out);
        $t = $Some2value($out);

        $newVarName1 = $LamT2var($t);
        $newVarName2 = $LamT2var($LamT2body($t));

        isnt($newVarName1, 'x', "fresh var $newVarName1 is different from var x");
        isnt($newVarName1, 'y', "fresh var $newVarName1 is different from var y");
        isnt($newVarName1, 'z', "fresh var $newVarName1 is different from var z");

        isnt($newVarName2, 'x', "fresh var $newVarName2 is different from var x");
        isnt($newVarName2, 'y', "fresh var $newVarName2 is different from var y");
        isnt($newVarName2, 'z', "fresh var $newVarName2 is different from var z");
        
        is_eq-Term($t, $LamT($newVarName1, $LamT($newVarName2, $AppT($AppT($VarT($newVarName2), $VarT($newVarName1)), `'x y'))), 
            '[(x y)/z](λy.λx.x y z)  =  (λα1.λα2.α2 α1 (x y))');
    }, 'plus additional alpha-conversions (fresh var for x and y)');
    
    subtest({ # [(x y)/z](λy.λx.x y z ((λz.λx.x y z) (λx.y x)))  =  (λα1.λα2.α2 α1 (x y) ((λz.λx.x α1 z) (λx.α1 x)))
        my ($out, $α1, $α2, $t, $keepfree);
        $keepfree = $cons('x', $cons('y', $nil));

        $out = $subst-with-alpha('z', `'x y', $keepfree, `'λy.λx.x y z ((λz.λx.x y z) (λx.y x))');
        diag lambdaArgToStr($out);
        $t = $Some2value($out);

        $α1 = $LamT2var($t);
        $α2 = $LamT2var($LamT2body($t));

        isnt($α1, 'x', "fresh var $α1 is different from var x");
        isnt($α1, 'y', "fresh var $α1 is different from var y");
        isnt($α1, 'z', "fresh var $α1 is different from var z");

        isnt($α2, 'x', "fresh var $α2 is different from var x");
        isnt($α2, 'y', "fresh var $α2 is different from var y");
        isnt($α2, 'z', "fresh var $α2 is different from var z");

        my $λx_α1x = $LamT('x', $AppT($VarT($α1), `'x'));
        my $λz_λx_xα1z = $LamT('z', $LamT('x', $AppT($AppT(`'x', $VarT($α1)), `'z')));
        my $α2α1_xy = $AppT($AppT($VarT($α2), $VarT($α1)), `'(x y)');

        
        is_eq-Term($t, $LamT($α1, $LamT($α2, $AppT($α2α1_xy, $AppT($λz_λx_xα1z, $λx_α1x)))),
            '[(x y)/z](λy.λx.x y z ((λz.λx.x y z) (λx.y x)))  =  (λα1.λα2.α2 α1 (x y) ((λz.λx.x α1 z) (λx.α1 x)))');
    }, 'plus additional alpha-conversions (fresh var for x and y, but omitting unnecessary alpha-conversions)');
}

