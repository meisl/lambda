use v6;
use Test;

use Lambda::BaseP6;
use Lambda::TermADT;

use Lambda::LambdaGrammar;
use Lambda::Conversion::Bool-conv;


our constant $testTerms is export = {
    my $time = now;

    my role Aka {
        has Str:D $.mainKey;
        has       @!names = @();

        method names    { @!names }
        method synonyms { @!names.grep(* ne $!mainKey) }
    }

    my class TestTerms {
        has %!hash   = %();
        has @.values = @();

        method new(%hash) {
            self.bless(:%hash)
        }

        submethod BUILD(:%!hash) {
            for %!hash.pairs -> (:$key, :$value) {
                $value does Aka($key);  # sets mainKey
                $value.names.push($key);
                @!values.push($value);
            }
        }

        # TODO: why is postcircumfix:<{ }>($key) not working ?!
        method get($key) {
            %!hash{$key}
        }

        method keys { @!values.map(*.names).flat }

        method aka(Str:D $mainKey, *@names) {
            my $val = self.get($mainKey);
            die "unknown main key {$mainKey.perl} while adding synonyms {@names.perl}"
                unless $val.defined;
            for @names {
                my $prev = self.get($_);
                if $prev.defined {
                    my @prevSyns = $prev.names.grep(* ne $prev.mainKey);
                    my $prevAkas = @prevSyns.elems == 0
                        ?? ''
                        !! ' (aka ' ~ @prevSyns.map(*.perl).join(', ') ~ ')';
                    my @valSyns = $val.names.grep(* ne $mainKey);
                    my $valAkas = ($val === $prev) || (@valSyns.elems == 0)
                        ?? ''
                        !! "\n    Note: `'{$mainKey}' is aka " ~ @valSyns.map(*.perl).join(', ');
                    die "cannot add synonym {$_.perl} for {$mainKey.perl}"
                        ~ " - {$_.perl} already maps to `'{$prev.mainKey}'$prevAkas$valAkas"
                    ;
                }
                #say "adding {$_.perl} as synonym for {$mainKey.perl} => {$Term2srcLess($val)}";
                %!hash{$_} ::= $val;
                $val.names.push($_);
            }
            return self;
        }

        method synonyms {
            @!values.grep(
                *.names.elems > 1
            ).map(-> $value {
                ".aka('{$value.mainKey}', '{$value.synonyms.join('\', \'')}')";
            }).join("\\\n        ");
        }
    }

    my $a  ::= $VarT('a');
    my $b  ::= $VarT('b');
#    my $c  ::= $VarT('c');     # clashes with c = ConstT("c")
    my $d  ::= $VarT('d');
    my $e  ::= $VarT('e');
    my $f  ::= $VarT('f');
    my $g  ::= $VarT('g');
    my $h  ::= $VarT('h');
    my $k  ::= $VarT('k');

    my $u  ::= $VarT('u');
    my $v  ::= $VarT('v');
    my $w  ::= $VarT('w');
    my $x  ::= $VarT('x');
    my $y  ::= $VarT('y');
    my $z  ::= $VarT('z');

    my $c  ::= $ConstT('c');

    my $f1 ::= $VarT('f1');
    my $f2 ::= $VarT('f2');
    my $f3 ::= $VarT('f3');
    my $f4 ::= $VarT('f4');
    my $f5 ::= $VarT('f5');

    my $fa ::= $AppT($f, $a);
    my $fb ::= $AppT($f, $b);
    my $fy ::= $AppT($f, $y);
    my $gh ::= $AppT($g, $h);
    my $gx ::= $AppT($g, $x);

    my $xx ::= $AppT($x, $x);
    my $xy ::= $AppT($x, $y);
    my $xz ::= $AppT($x, $z);
    my $xc ::= $AppT($x, $c);

    my $yx ::= $AppT($y, $x);
    my $yy ::= $AppT($y, $y);
    my $yz ::= $AppT($y, $z);
    my $yc ::= $AppT($y, $c);

    my $zx ::= $AppT($z, $x);
    my $zy ::= $AppT($z, $y);
    my $zz ::= $AppT($z, $z);
    my $zc ::= $AppT($z, $c);

    my $fab ::= $AppT($fa, $b);
    my $fba ::= $AppT($fb, $a);
    my $fyx ::= $AppT($fy, $x);
    my $xyz ::= $AppT($xy, $z);
    my $xyc ::= $AppT($xy, $c);

    my $xyzx ::= $AppT($xyz, $x);

    my $hf1             ::= $AppT($h, $f1);
    my $hf1f2           ::= $AppT($hf1, $f2);
    my $hf1f2f3         ::= $AppT($hf1f2, $f3);
    my $hf1f2f3f4       ::= $AppT($hf1f2f3, $f4);
    my $hf1f2f3f4f5     ::= $AppT($hf1f2f3f4, $f5);

    my $L__x  ::= $LamT('_', $x);
    my $Lx_x  ::= $LamT('x', $x);
    my $Lx_c  ::= $LamT('x', $c);
    my $Lx_xx ::= $LamT('x', $xx);
    my $Lx_xy ::= $LamT('x', $xy);
    my $Lx_xc ::= $LamT('x', $xc);
    my $Lx_yx ::= $LamT('x', $yx);

    my $L__y  ::= $LamT('_', $y);
    my $Ly_xx ::= $LamT('y', $xx);
    my $Ly_xy ::= $LamT('y', $xy);
    my $Ly_yy ::= $LamT('y', $yy);
    my $Ly_zy ::= $LamT('y', $zy);
    my $Ly_Ky ::= $LamT('y', $L__y);
    
    my $Ik    ::= $AppT($Lx_x, $k);
    my $Ikf1  ::= $AppT($Ik, $f1);
    my $Lk_Ikf1  ::= $LamT('k', $Ikf1);

    my $θB ::= $LamT('f', $LamT('g', $LamT('x', $AppT($f, $gx))));   #   B aka compose
    my $θC ::= $LamT('f', $LamT('x', $LamT('y', $fyx)));             #   C aka swap-args

    my $θnil  ::= $LamT('h', $LamT('_', $h));
    my $θcons ::= $LamT('f1', $LamT('f2', $LamT('_', $LamT('h', $hf1f2))));

    my $θCθcons     ::= $AppT($θC, $θcons);
    my $θCθconsθnil ::= $AppT($θCθcons, $θnil);

    my $out = TestTerms.new({
        'f1'                        => $f1,
        'f2'                        => $f2,
        'f3'                        => $f3,
        'f4'                        => $f4,
        'f5'                        => $f5,

        'a'                         => $a,
        'b'                         => $b,
#        'c'                         => $c,     # clashes with c = ConstT("c")
        'd'                         => $d,
        'e'                         => $e,
        'f'                         => $f,
        'g'                         => $g,
        'h'                         => $h,
        'k'                         => $k,

        'u'                         => $u,
        'v'                         => $v,
        'w'                         => $w,
        'x'                         => $x,
        'y'                         => $y,
        'z'                         => $z,
        '"c"'                       => $c,
        '5'                         => $ConstT(5),

        '(g h)'                     => $gh,
        '(g x)'                     => $gx,
        '(f y)'                     => $fy,

        '(x x)'                     => $xx,
        '(x y)'                     => $xy,
        '(x z)'                     => $xz,
        '(x "c")'                   => $xc,

        '(y x)'                     => $yx,
        '(y y)'                     => $yy,
        '(y z)'                     => $yz,
        '(y "c")'                   => $yc,

        '(z x)'                     => $zx,
        '(z y)'                     => $zy,
        '(z z)'                     => $zz,
        '(z "c")'                   => $zc,

        '((f a) b)'                 => $fab,
        '((f b) a)'                 => $fba,
        '((f y) x)'                 => $fyx,
        '((x y) z)'                 => $xyz,
        '((x y) "c")'               => $xyc,
        '(((x y) z) x)'             => $xyzx,
        '(x (y z))'                 => $AppT($x, $yz),
        '((x (y z)) x)'             => $AppT($AppT($x, $yz), $x),
        '(x (y (z x)))'             => $AppT($x, $AppT($y, $zx)),
        '((x y) (y z))'             => $AppT($xy, $yz),

        '(λ_.x)'                    => $L__x,
        '(λx."c")'                  => $Lx_c,
        '(λx.x)'                    => $Lx_x,   # I aka id
        '((λx.x) k)'                => $Ik,
        '(((λx.x) k) f1)'           => $Ikf1,
        '(λk.(((λx.x) k) f1))'      => $Lk_Ikf1,
        '(λf.(λg.(λx.(f (g x)))))'  => $θB,
        '(λf.(λx.(λy.((f y) x))))'  => $θC,
        '(λf.(λa.(λb.((f b) a))))'  => $LamT('f', $LamT('a', $LamT('b', $fba))),    # alpha-converted C

        '(λx.(λ_.x))'               => $LamT('x', $L__x),   # K aka const
        '(λx.(x "c"))'              => $Lx_xc,
        '(λx.(x x))'                => $Lx_xx,  # omegaX aka ωX ("omega in x") aka ω aka omega
        '(λx.(x y))'                => $Lx_xy,
        '(λx.(y x))'                => $Lx_yx,
        '(λx.((x y) "c"))'          => $LamT('x', $xyc),

        '(λ_.y)'                    => $L__y,
        '(λy.(x x))'                => $Ly_xx,
        '(λy.(x y))'                => $Ly_xy,
        '(λy.(y y))'                => $Ly_yy,   # omegaY aka ωY ("omega in y")
        '(λy.(z y))'                => $Ly_zy,
        '(λy.(λ_.y))'               => $Ly_Ky,

        '(λg.(λh.((λy.(λ_.y)) (g h))))' => $LamT('g', $LamT('h', $AppT($Ly_Ky, $gh))),

        '(h f1)'                        => $hf1,
        '((h f1) f2)'                   => $hf1f2,
        '(((h f1) f2) f3)'              => $hf1f2f3,
        '((((h f1) f2) f3) f4)'         => $hf1f2f3f4,
        '(((((h f1) f2) f3) f4) f5)'    => $hf1f2f3f4f5,

        '(λh.(λ_.h))'                       =>  $LamT('h', $LamT('_', $h)),                                 # ctor1o2f0 (ctor 1 of 2 with 0 fields)
        '(λ_.(λh.h))'                       =>  $LamT('_', $LamT('h', $h)),                                 # ctor2o2f0 (ctor 2 of 2 with 0 fields)
        '(λf1.(λh.(λ_.(h f1))))'            =>  $LamT('f1', $LamT('h', $LamT('_', $hf1))),                  # ctor1o2f1 (ctor 1 of 2 with 1 field)
        '(λf1.(λ_.(λh.(h f1))))'            =>  $LamT('f1', $LamT('_', $LamT('h', $hf1))),                  # ctor2o2f1 (ctor 2 of 2 with 1 field)
        '(λf1.(λf2.(λh.(λ_.((h f1) f2)))))' =>  $LamT('f1', $LamT('f2', $LamT('h', $LamT('_', $hf1f2)))),   # ctor1o2f2 (ctor 1 of 2 with 2 fields)
        '(λf1.(λf2.(λ_.(λh.((h f1) f2)))))' =>  $LamT('f1', $LamT('f2', $LamT('_', $LamT('h', $hf1f2)))),   # ctor2o2f2 (ctor 1 of 2 with 2 fields)

        '(((λf.(λg.(λx.(f (g x))))) ((λf.(λx.(λy.((f y) x)))) (λf1.(λf2.(λ_.(λh.((h f1) f2))))))) (((λf.(λx.(λy.((f y) x)))) (λf1.(λf2.(λ_.(λh.((h f1) f2)))))) (λh.(λ_.h))))'
            => $AppT($AppT($θB, $θCθcons), $θCθconsθnil),
        # aka 'B (C cons) (C cons nil)'

        '(λa.(λb.(((λf1.(λf2.(λ_.(λh.((h f1) f2))))) a) (((λf1.(λf2.(λ_.(λh.((h f1) f2))))) b) (λh.(λ_.h))))))'
            => $LamT('a', $LamT('b', $AppT($AppT($θcons, $a), $AppT($AppT($θcons, $b), $θnil)))),
        # aka 'λa.λb.cons a (cons b nil)'

        '(λx.(λy.(((λf1.(λf2.(λ_.(λh.((h f1) f2))))) x) (((λf1.(λf2.(λ_.(λh.((h f1) f2))))) y) (λh.(λ_.h))))))'
            => $LamT('x', $LamT('y', $AppT($AppT($θcons, $x), $AppT($AppT($θcons, $y), $θnil)))),
        # aka 'λx.λy.cons x (cons y nil)'

        '((x y) (λy.(x y)))'        => $AppT($xy, $Ly_xy),

        '((λx.(y x)) (x y))'            => $AppT($Lx_yx, $xy),
        '(((λx.(y x)) (x y)) x)'        => $AppT($AppT($Lx_yx, $xy), $x),
        '(((λx.(y x)) (x y)) (λx.x))'   => $AppT($AppT($Lx_yx, $xy), $Lx_x),
        '(((λx.(y x)) (λx.x)) (λx.x))'  => $AppT($AppT($Lx_yx, $Lx_x), $Lx_x),

        '((λx.x) x)'                    => $AppT($Lx_x, $x),
        '((λx.(y x)) (λy.(x y)))'       => $AppT($Lx_yx, $Ly_xy),
        '(λx.(x (λy.(x y))))'           => $LamT('x', $AppT($x, $Ly_xy)),
        '((λy.(x y)) y)'                => $AppT($Ly_xy, $y),
        '(λx.((λy.(z y)) x))'           => $LamT('x', $AppT($Ly_zy, $x)),
        '(λx.((λy.(x y)) x))'           => $LamT('x', $AppT($Ly_xy, $x)),
        '(λx.((λx.(x y)) x))'           => $LamT('x', $AppT($Lx_xy, $x)),
        '((λx.(x x)) (y y))'            => $AppT($Lx_xx, $yy),
        '((y y) (λx.(x x)))'            => $AppT($yy, $Lx_xx),
        '(x (x y))'                     => $AppT($x, $xy),
        '(x (λy.(x y)))'                => $AppT($VarT("x"), $Ly_xy),

        '(λx.((λy.(z y)) (x x)))'       => $LamT("x", $AppT($Ly_zy, $xx)),
        '(λz.(x (x y)))'                => $LamT('z', $AppT($x, $xy)),
        '(λz.(x (λy.(x y))))'           => $LamT("z", $AppT($VarT("x"), $Ly_xy)),

        '((λx.(x x)) (λx.(x x)))'       => $AppT($Lx_xx, $Lx_xx), # = (ωX ωX) aka ΩXX ("Omega in x") aka Ω aka Omega
        '((λy.(y y)) (λy.(y y)))'       => $AppT($Ly_yy, $Ly_yy), # = (ωY ωY) aka ΩYY ("Omega in y")
        '((λx.(x x)) (λy.(y y)))'       => $AppT($Lx_xx, $Ly_yy), # = (ωX ωY) aka ΩXY (same as Ω modulo α-conversion)
        '((λy.(y y)) (λx.(x x)))'       => $AppT($Ly_yy, $Lx_xx), # = (ωY ωX) aka ΩYX (same as Ω modulo α-conversion)
        '((λx.(x x)) (λy.(x x)))'       => $AppT($Lx_xx, $Ly_xx), # NOT Ω (wrong binder in 2nd λ)
    });

    # some synonyms:
    $out\
#        .aka('(λx.x)', <I id>)\
#        .aka('(λx.(λ_.x))', <K const>)\
#        .aka('(λf.(λg.(λx.(f (g x)))))', <B compose>, 'λf.λg.λx.f (g x)', 'λf.(λg.(λx.(f (g x))))')\
#        .aka('(λf.(λx.(λy.((f y) x))))', <C swap-args>, 'λf.λx.λy.f y x', 'λf.(λx.(λy.((f y) x)))')\

#        .aka('(λh.(λ_.h))'                      , <ctor1o2f0 nil None>, 'λh.(λ_.h)'                      , 'λh.λ_.h'              )\
#        .aka('(λ_.(λh.h))'                      , <ctor2o2f0>,          'λ_.(λh.h)'                      , 'λ_.λh.h'              )\
#        .aka('(λf1.(λh.(λ_.(h f1))))'           , <ctor1o2f1>,          'λf1.(λh.(λ_.(h f1)))'           , 'λf1.λh.λ_.h f1'       )\
#        .aka('(λf1.(λ_.(λh.(h f1))))'           , <ctor2o2f1 Some>,     'λf1.(λ_.(λh.(h f1)))'           , 'λf1.λ_.λh.h f1'       )\
#        .aka('(λf1.(λf2.(λh.(λ_.((h f1) f2)))))', <ctor1o2f2>,          'λf1.(λf2.(λh.(λ_.((h f1) f2))))', 'λf1.λf2.λh.λ_.h f1 f2')\
#        .aka('(λf1.(λf2.(λ_.(λh.((h f1) f2)))))', <ctor2o2f2 cons>,     'λf1.(λf2.(λ_.(λh.((h f1) f2))))', 'λf1.λf2.λ_.λh.h f1 f2')\

#        
#        .aka('(λx.(x x))', <ωX omegaX ω omega>)\
#        .aka('(λy.(y y))', <ωY omegaY>)\
#        
#        .aka('((λx.(x x)) (λx.(x x)))', <ΩXX OmegaXX Ω Omega>, '(ωX ωX)', '(omegaX omegaX)', '(ω ω)', '(omega omega)')\
#        .aka('((λy.(y y)) (λy.(y y)))', <ΩYY OmegaYY>,         '(ωY ωY)', '(omegaY omegaY)')\
#        .aka('((λx.(x x)) (λy.(y y)))', <ΩXY OmegaXY>,         '(ωX ωY)', '(omegaX omegaY)')\
#        .aka('((λy.(y y)) (λx.(x x)))', <ΩYX OmegaYX>,         '(ωY ωX)', '(omegaY omegaX)')\

# -----------------------------------------------------------------------------
        .aka('(x x)', 'x x')\
        .aka('(λf.(λg.(λx.(f (g x)))))', <B compose>, 'λf.λg.λx.f (g x)', 'λf.(λg.(λx.(f (g x))))')\
        .aka('(λf.(λx.(λy.((f y) x))))', <C swap-args>, 'λf.λx.λy.f y x', 'λf.(λx.(λy.((f y) x)))')\
        .aka('(λf.(λa.(λb.((f b) a))))', 'λf.(λa.(λb.((f b) a)))', 'λf.λa.λb.f b a', '(λf.λa.λb.f b a)')\

        .aka('(λh.(λ_.h))'                      , <ctor1o2f0 nil None>, 'λh.(λ_.h)'                      , 'λh.λ_.h'              )\
        .aka('(λ_.(λh.h))'                      , <ctor2o2f0>,          'λ_.(λh.h)'                      , 'λ_.λh.h'              )\
        .aka('(λf1.(λh.(λ_.(h f1))))'           , <ctor1o2f1>,          'λf1.(λh.(λ_.(h f1)))'           , 'λf1.λh.λ_.h f1'       )\
        .aka('(λf1.(λ_.(λh.(h f1))))'           , <ctor2o2f1 Some>,     'λf1.(λ_.(λh.(h f1)))'           , 'λf1.λ_.λh.h f1'       )\
        .aka('(λf1.(λf2.(λh.(λ_.((h f1) f2)))))', <ctor1o2f2>,          'λf1.(λf2.(λh.(λ_.((h f1) f2))))', 'λf1.λf2.λh.λ_.h f1 f2')\
        .aka('(λf1.(λf2.(λ_.(λh.((h f1) f2)))))', <ctor2o2f2 cons>,     'λf1.(λf2.(λ_.(λh.((h f1) f2))))', 'λf1.λf2.λ_.λh.h f1 f2')\

        .aka('(((λf.(λg.(λx.(f (g x))))) ((λf.(λx.(λy.((f y) x)))) (λf1.(λf2.(λ_.(λh.((h f1) f2))))))) (((λf.(λx.(λy.((f y) x)))) (λf1.(λf2.(λ_.(λh.((h f1) f2)))))) (λh.(λ_.h))))',
             '(λf.λg.λx.f (g x)) ((λf.λx.λy.f y x) (λf1.λf2.λ_.λh.h f1 f2)) ((λf.λx.λy.f y x) (λf1.λf2.λ_.λh.h f1 f2) (λh.λ_.h))',
             'B (C cons) (C cons nil)', '(B (C cons) (C cons nil))', '((B (C cons)) ((C cons) nil))')\

        .aka('(λa.(λb.(((λf1.(λf2.(λ_.(λh.((h f1) f2))))) a) (((λf1.(λf2.(λ_.(λh.((h f1) f2))))) b) (λh.(λ_.h))))))',
             'λa.λb.(λf1.λf2.λ_.λh.h f1 f2) a ((λf1.λf2.λ_.λh.h f1 f2) b (λh.λ_.h))',
             'λa.λb.cons a (cons b nil)', '(λa.λb.cons a (cons b nil))', 'λa.(λb.((cons a) ((cons b) nil)))', '(λa.(λb.((cons a) ((cons b) nil))))')\

        .aka('(λx.(λy.(((λf1.(λf2.(λ_.(λh.((h f1) f2))))) x) (((λf1.(λf2.(λ_.(λh.((h f1) f2))))) y) (λh.(λ_.h))))))',
             'λx.λy.(λf1.λf2.λ_.λh.h f1 f2) x ((λf1.λf2.λ_.λh.h f1 f2) y (λh.λ_.h))',
             'λx.λy.cons x (cons y nil)', '(λx.λy.cons x (cons y nil))', 'λx.(λy.((cons x) ((cons y) nil)))', '(λx.(λy.((cons x) ((cons y) nil))))')\

        .aka('(h f1)', 'h f1')\
        .aka('((h f1) f2)', 'h f1 f2')\
        .aka('(((h f1) f2) f3)', 'h f1 f2 f3')\
        .aka('((((h f1) f2) f3) f4)', 'h f1 f2 f3 f4')\
        .aka('(((((h f1) f2) f3) f4) f5)', 'h f1 f2 f3 f4 f5')\
        .aka('(f y)', 'f y')\
        .aka('(g h)', 'g h')\
        .aka('(g x)', 'g x')\
        .aka('(x y)', 'x y')\
        .aka('(x z)', 'x z')\
        .aka('(x "c")', 'x "c"')\
        .aka('(y x)', 'y x')\
        .aka('(y y)', 'y y')\
        .aka('(y z)', 'y z')\
        .aka('(y "c")', 'y "c"')\
        .aka('(z x)', 'z x')\
        .aka('(z y)', 'z y')\
        .aka('(z z)', 'z z')\
        .aka('(z "c")', 'z "c"')\
        .aka('((f a) b)', '(f a) b', '(f a b)', 'f a b')\
        .aka('((f b) a)', '(f b) a', '(f b a)', 'f b a')\
        .aka('((f y) x)', '(f y) x', '(f y x)', 'f y x')\
        .aka('((x y) z)', '(x y) z', '(x y z)', 'x y z')\
        .aka('((x y) "c")', '(x y) "c"', '(x y "c")', 'x y "c"')\
        .aka('(((x y) z) x)', '((x y) z) x', '(x y z x)', 'x y z x')\
        .aka('(x (y z))', 'x (y z)')\
        .aka('((x (y z)) x)', '(x (y z)) x', '(x (y z) x)', 'x (y z) x')\
        .aka('(x (y (z x)))', 'x (y (z x))')\
        .aka('((x y) (y z))', '(x y) (y z)', '(x y (y z))', 'x y (y z)')\
        .aka('(λ_.x)', 'λ_.x')\
        .aka('(λ_.y)', 'λ_.y')\
        .aka('(λx."c")', 'λx."c"')\
        .aka('(λx.x)', 'I', 'id', 'λx.x')\
        .aka('((λx.x) k)', '(λx.x) k')\
        .aka('(((λx.x) k) f1)', '((λx.x) k) f1', '(λx.x) k f1')\
        .aka('(λk.(((λx.x) k) f1))', 'λk.(((λx.x) k) f1)', 'λk.(λx.x) k f1')\
        .aka('(λx.(λ_.x))', 'K', 'const', 'λx.(λ_.x)', 'λx.λ_.x')\
        .aka('(λy.(λ_.y))', 'λy.(λ_.y)', 'λy.λ_.y')\
        .aka('(λg.(λh.((λy.(λ_.y)) (g h))))', 'λg.(λh.((λy.(λ_.y)) (g h)))', 'λg.λh.(λy.λ_.y) (g h)')\
        .aka('(λx.(x "c"))', 'λx.(x "c")', 'λx.x "c"')\
        .aka('(λx.(x x))', 'ωX', 'omegaX', 'ω', 'omega', 'λx.(x x)', 'λx.x x')\
        .aka('(λx.(x y))', 'λx.(x y)', 'λx.x y')\
        .aka('(λx.(y x))', 'λx.(y x)', 'λx.y x')\
        .aka('(λx.((x y) "c"))', 'λx.((x y) "c")', 'λx.x y "c"')\
        .aka('(λy.(x x))', 'λy.(x x)', 'λy.x x')\
        .aka('(λy.(x y))', 'λy.(x y)', 'λy.x y')\
        .aka('(λy.(y y))', 'ωY', 'omegaY', 'λy.(y y)', 'λy.y y')\
        .aka('(λy.(z y))', 'λy.(z y)', 'λy.z y')\
        .aka('((x y) (λy.(x y)))', '(x y) (λy.(x y))', '(x y (λy.x y))', 'x y (λy.x y)')\
        .aka('((λx.(y x)) (x y))', '(λx.(y x)) (x y)', '(λx.y x) (x y)')\
        .aka('(((λx.(y x)) (x y)) x)', '((λx.(y x)) (x y)) x', '(λx.y x) (x y) x')\
        .aka('(((λx.(y x)) (x y)) (λx.x))', '((λx.(y x)) (x y)) (λx.x)', '(λx.y x) (x y) (λx.x)')\
        .aka('(((λx.(y x)) (λx.x)) (λx.x))', '((λx.(y x)) (λx.x)) (λx.x)', '(λx.y x) (λx.x) (λx.x)')\
        .aka('((λx.x) x)', '(λx.x) x')\
        .aka('((λx.(y x)) (λy.(x y)))', '(λx.(y x)) (λy.(x y))', '(λx.y x) (λy.x y)')\
        .aka('(λx.(x (λy.(x y))))', 'λx.(x (λy.(x y)))', 'λx.x (λy.x y)')\
        .aka('((λy.(x y)) y)', '(λy.(x y)) y', '(λy.x y) y')\
        .aka('(λx.((λy.(z y)) x))', 'λx.((λy.(z y)) x)', 'λx.(λy.z y) x')\
        .aka('(λx.((λy.(x y)) x))', 'λx.((λy.(x y)) x)', 'λx.(λy.x y) x')\
        .aka('(λx.((λx.(x y)) x))', 'λx.((λx.(x y)) x)', 'λx.(λx.x y) x')\
        .aka('((λx.(x x)) (y y))', '(λx.(x x)) (y y)', '(λx.x x) (y y)')\
        .aka('((y y) (λx.(x x)))', '(y y) (λx.(x x))', '(y y (λx.x x))', 'y y (λx.x x)')\
        .aka('(x (x y))', 'x (x y)')\
        .aka('(x (λy.(x y)))', 'x (λy.(x y))', '(x (λy.x y))', 'x (λy.x y)')\
        .aka('(λx.((λy.(z y)) (x x)))', 'λx.((λy.(z y)) (x x))', 'λx.(λy.z y) (x x)')\
        .aka('(λz.(x (x y)))', 'λz.(x (x y))', 'λz.x (x y)')\
        .aka('(λz.(x (λy.(x y))))', 'λz.(x (λy.(x y)))', 'λz.x (λy.x y)')\
        .aka('((λx.(x x)) (λx.(x x)))', 'ΩXX', 'OmegaXX', 'Ω', 'Omega', '(ωX ωX)', '(omegaX omegaX)', '(ω ω)', '(omega omega)', '(λx.(x x)) (λx.(x x))', 'ωX ωX', 'omegaX omegaX', 'ω ω', 'omega omega', '(λx.x x) (λx.x x)')\
        .aka('((λy.(y y)) (λy.(y y)))', 'ΩYY', 'OmegaYY', '(ωY ωY)', '(omegaY omegaY)', '(λy.(y y)) (λy.(y y))', 'ωY ωY', 'omegaY omegaY', '(λy.y y) (λy.y y)')\
        .aka('((λx.(x x)) (λy.(y y)))', 'ΩXY', 'OmegaXY', '(ωX ωY)', '(omegaX omegaY)', '(λx.(x x)) (λy.(y y))', 'ωX ωY', 'omegaX omegaY', '(λx.x x) (λy.y y)')\
        .aka('((λy.(y y)) (λx.(x x)))', 'ΩYX', 'OmegaYX', '(ωY ωX)', '(omegaY omegaX)', '(λy.(y y)) (λx.(x x))', 'ωY ωX', 'omegaY omegaX', '(λy.y y) (λx.x x)')\
        .aka('((λx.(x x)) (λy.(x x)))', '(λx.(x x)) (λy.(x x))', '(λx.x x) (λy.x x)', '((λx.x x) (λy.x x))')\
;

#`{
    # for convenience: make stuff available without surrounding parens as well
    for $out.keys -> $key {
        if $key.substr(0, 1) eq '(' {
            $out.aka($key, $key.substr(1, *-1));
        }
    }
    for $out.values -> $value {
        my $mainKey = $value.mainKey;
        my @synonyms = set($Term2srcFull($value), $Term2srcLess($value), $Term2srcLesser($value)
        ).keys.grep(* ne any($value.names));
        #say "$mainKey => {@synonyms.perl}";
        $out.aka($mainKey, |@synonyms);
    }
}

    $time = (now.Real - $time.Real).round(0.01);
    diag "$time sec consumed for test-terms initialization";

#    say '    $out' ~ $out.synonyms;
    $out;
}();


#`{
    my $maxKeyLen = @(0, %terms.keys).reduce(-> $currentMax, $key { max($currentMax, $key.chars) });
    my $termsSrcP6 = %terms.pairs.map(-> (:$key, :$value) {
        sprintf("%-{$maxKeyLen+3}s => %s", "'$key'", $Term2sourceP6($value));
     }).join(",\n    ");
    $termsSrcP6 = '%(' ~ "\n    " ~ $termsSrcP6 ~ "\n);";
    diag "our \%terms is export = $termsSrcP6";

    diag "termCount: {%terms.elems}";
    diag "maxKeyLen: $maxKeyLen";
}


multi sub prefix:<`>(Str:D $termIdentifier -->TTerm:D) is export {
    my $term = $testTerms.get($termIdentifier);
    if not $term.defined {
        my $msg = "unprepared test-term: '$termIdentifier'";
        try {
            $term = parseLambda($termIdentifier);
            my $syn = $testTerms.values.first(-> $t { convertTBool2P6Bool($Term-eq($term, $t)) });
            if $syn.defined {
                $msg ~= " - but it's a synonym; in {$?FILE}:\n    .aka('{$syn.mainKey}', '$termIdentifier')\\";
            } else {
                $msg ~= " - you may want to add it to in {$?FILE}:\n    '$termIdentifier'         => {$Term2sourceP6($term)},";
            }
        }
        $msg ~= " - $!"
            if $!;
        die $msg;
    }
    return $term;
}

sub testTermFn($f, :$argToStr = *.Str, :$expectedToStr, *@tests) is export {
    my Str $fgist = $f.gist;
    subtest({
        for @tests -> $test {
            my Any   $arg = $test.key;
            
            my TTerm $term;
            my Str   $termSrc;
            if $arg ~~ Str {
                $term    = `$arg;
                $termSrc = $Term2source($term);
            } elsif $arg ~~ TTerm {
                $term    = $arg;
                $termSrc = $Term2source($term);
                # we got a new one - add it!        # <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<
                $testTerms{$termSrc} = $term;      # <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<
            } else {
                die "expected either a TTerm or a Str but got $arg.perl";
            }

            my Str   $argStr        = $argToStr($arg);
            my Any   $expected      = $test.value;
            my Str   $expectedStr   = $expectedToStr.defined
                                        ?? ' -> ' ~ $expectedToStr($expected)
                                        !! '';
            my $desc = "($fgist $argStr)$expectedStr";

            is($f($term), $expected, $desc);
        }
    }, "$fgist on various inputs");
}

my sub fail-Term_eq(Str:D $msg, TTerm:D $actual, TTerm:D $expected, Bool :$full = False) {
    my $actualSrc = ($full ?? $Term2srcLess !! $Term2srcFull)($actual);
    my $actualStr = $actual.Str;
    my $expectedSrc = ($full ?? $Term2srcLess !! $Term2srcFull)($expected);
    my $expectedStr = $expected.Str;
    my $n = max($actualSrc.chars, $expectedSrc.chars);
    diag sprintf("expected: `%-{$n}s   /   %s\n     got: `%-{$n}s   /   %s",
        $expectedSrc, $expectedStr,
        $actualSrc,   $actualStr
    );
    ok(False, $msg);
}

sub is_eq-Term(TTerm:D $actual, TTerm:D $expected, Str $msg?, Bool :$full = False) is export {
    my $m = $msg // "`({$Term2srcLesser($actual)})  should equal  `({$Term2srcLesser($expected)})";
    if convertTBool2P6Bool($Term-eq($actual, $expected)) {
        ok(True, $m);
    } else {
        fail-Term_eq($m, $actual, $expected, :$full);
    }
}
