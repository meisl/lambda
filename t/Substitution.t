use v6;
use Test;
use Test::Util;
use Test::Util_Lambda;
use Test::Util_Term;

use Lambda::Boolean;
use Lambda::MaybeADT;
use Lambda::ListADT;
use Lambda::PairADT;
use Lambda::TermADT;

use Lambda::Conversion;


# module under test:
use Lambda::Substitution;

plan 7;


{ # function (subst inTerm whatTerm forVar)
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


{ # function (subst-with-alpha forVar whatTerm keepfree alpha-convs inTerm)
    is_properLambdaFn $subst-with-alpha, 'subst-with-alpha';

    testTermFn($subst-with-alpha,
        [`'x', `'y',        [`'y'],         `'"c"' ] => $None,

        [`'x', `'y',        [`'y'],         `'y'   ] => $None,
        [`'x', `'y',        [`'y'],         `'x'   ] => $Some(`'y'),

        [`'x', `'y',        [`'y'],         `'x x' ] => $Some(`'y y'),

        [`'z', `'y',        [`'y'],         `'x y' ] => $None,
        [`'x', `'y',        [`'y'],         `'x y' ] => $Some(`'y y'),
        [`'y', `'x',        [`'x'],         `'x y' ] => $Some(`'x x'),
                           
        [`'z', `'y',        [`'y'],         `'λx.y'] => $None,
        [`'y', `'z',        [`'z'],         `'λx.y'] => $Some(`'λx.z'),

        # main subst var x NOT free in body:
        [`'x', `'z',        [`'z'],         `'λx.x y' ] => $None,
        
        # main subst var y IS free in body:
        [`'y', `'z',        [`'z'],         `'λx.x y' ] => $Some(`'λx.x z'),  # ...*except* for the lambda's binder!

        # neither forVar nor var free in body, and no external alpha-convs applicable
        [`'v', `'x y',   [`'x', `'y'],     `'λu.x y z'] => $None,
    );
    
    subtest({ # [(x y)/y](λx.x y z)  =  (λα1.α1 (x y) z)
        my ($out, $newVarName, $newVar, $newBody, $keepfree);
        $keepfree = $cons(`'x', $cons(`'y', $nil));
        
        $out = $Some2value($subst-with-alpha(`'y', `'x y', $keepfree, `'λx.x y z'));
        
        $newVarName = $LamT2var($out);    # DONE: LamT_ctor_with_Str_binder
        $newVar     = $VarT($newVarName);
        $newBody    = $LamT2body($out);

        isnt($newVarName, 'x', "fresh var $newVar is different from var x");
        isnt($newVarName, 'y', "fresh var $newVar is different from var y");
        isnt($newVarName, 'z', "fresh var $newVar is different from var z");
        
        is($newBody, $AppT($AppT($newVar, `'x y'), `'z'), '[(x y)/y](λx.x y z)  =  (λα1.α1 (x y) z)')
            or diag("     got: " ~ $Term2source($out));
    }, 'plus additional alpha-conversion (fresh var for x)');
}