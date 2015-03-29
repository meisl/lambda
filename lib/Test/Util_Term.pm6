use v6;
use Test;

use Lambda::BaseP6;
use Lambda::TermADT;

use Lambda::LambdaGrammar;
use Lambda::Conversion;


our constant $testTerms is export = {
    my $time = now;

    my role Aka {
        has Str:D $.mainKey;
        has       @!names = @();

        method names    { @!names }
        method synonyms { @!names.grep(* ne $!mainKey) }
    }

    my class TestTerms {
        has      %!hash   = %();
        has      @.values = @();
        has Real $.constructionTime is rw;

        method new(%h) {
            self.bless(:%h)
        }

        submethod BUILD(:%h) {
            for %h.pairs -> (:$key, :$value) {
                my $prev = %!hash{$key};
                if $prev.defined {
                    die "duplicate key $key => {$Term2srcLess($value)}  -  already maps to {$Term2srcLess($prev)}"
                }
                $value does Aka($key);  # sets mainKey
                $value.names.push($key);
                %!hash{$key} = $value;
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

    my $a    ::= $VarT('a');
    my $b    ::= $VarT('b');
    my $c    ::= $VarT('c');
    my $d    ::= $VarT('d');
    my $e    ::= $VarT('e');
    my $f    ::= $VarT('f');
    my $f1   ::= $VarT('f1');
    my $f2   ::= $VarT('f2');
    my $f3   ::= $VarT('f3');
    my $f4   ::= $VarT('f4');
    my $f5   ::= $VarT('f5');
    my $g    ::= $VarT('g');
    my $h    ::= $VarT('h');
    my $k    ::= $VarT('k');

    my $u    ::= $VarT('u');
    my $v    ::= $VarT('v');
    my $w    ::= $VarT('w');
    my $x    ::= $VarT('x');
    my $y    ::= $VarT('y');
    my $z    ::= $VarT('z');

    my $κc   ::= $ConstT('c');
    my $κ5   ::= $ConstT(5);

    my $fa   ::= $AppT($f, $a);
    my $fb   ::= $AppT($f, $b);
    my $fy   ::= $AppT($f, $y);
    my $gh   ::= $AppT($g, $h);
    my $gx   ::= $AppT($g, $x);

    my $uu   ::= $AppT($u, $u);

    my $xu   ::= $AppT($x, $u);
    my $xx   ::= $AppT($x, $x);
    my $xy   ::= $AppT($x, $y);
    my $xz   ::= $AppT($x, $z);
    my $xκc  ::= $AppT($x, $κc);

    my $yu   ::= $AppT($y, $u);
    my $yx   ::= $AppT($y, $x);
    my $yy   ::= $AppT($y, $y);
    my $yz   ::= $AppT($y, $z);
    my $yκc  ::= $AppT($y, $κc);

    my $zu   ::= $AppT($z, $u);
    my $zx   ::= $AppT($z, $x);
    my $zy   ::= $AppT($z, $y);
    my $zz   ::= $AppT($z, $z);
    my $zκc  ::= $AppT($z, $κc);

    my $fab  ::= $AppT($fa, $b);
    my $fba  ::= $AppT($fb, $a);
    my $fyx  ::= $AppT($fy, $x);
    my $xyz  ::= $AppT($xy, $z);
    my $xyκc ::= $AppT($xy, $κc);

    my $xyzx ::= $AppT($xyz, $x);

    my $hf1             ::= $AppT($h, $f1);
    my $hf1f2           ::= $AppT($hf1, $f2);
    my $hf1f2f3         ::= $AppT($hf1f2, $f3);
    my $hf1f2f3f4       ::= $AppT($hf1f2f3, $f4);
    my $hf1f2f3f4f5     ::= $AppT($hf1f2f3f4, $f5);

    my $λv_uu   ::= $LamT('v', $uu);
    my $λv_xu   ::= $LamT('v', $xu);
    my $λv_yu   ::= $LamT('v', $yu);
    my $λv_zu   ::= $LamT('v', $zu);
    my $λ__x    ::= $LamT('_', $x);
    my $λx_x    ::= $LamT('x', $x);
    my $λx_y    ::= $LamT('x', $y);
    my $λx_z    ::= $LamT('x', $z);
    my $λx_κc   ::= $LamT('x', $κc);
    my $λx_xx   ::= $LamT('x', $xx);
    my $λx_xy   ::= $LamT('x', $xy);
    my $λx_xz   ::= $LamT('x', $xz);
    my $λx_xκc  ::= $LamT('x', $xκc);
    my $λx_yx   ::= $LamT('x', $yx);

    my $λu_xyz  ::= $LamT('u', $xyz);
    my $λx_xyz  ::= $LamT('x', $xyz);

    my $λ__y    ::= $LamT('_', $y);
    my $λy_xx   ::= $LamT('y', $xx);
    my $λy_xy   ::= $LamT('y', $xy);
    my $λy_yy   ::= $LamT('y', $yy);
    my $λy_zy   ::= $LamT('y', $zy);

    my $λu_λv_uu    ::= $LamT('u', $λv_uu);
    my $λu_λv_xu    ::= $LamT('u', $λv_xu);
    my $λu_λv_yu    ::= $LamT('u', $λv_yu);
    my $λu_λv_zu    ::= $LamT('u', $λv_zu);
    my $λw_λx_xy    ::= $LamT('w', $λx_xy);
    my $λw_λx_xz    ::= $LamT('w', $λx_xz);

    my $λy_λ__y     ::= $LamT('y', $λ__y);
    my $λx_λ__x     ::= $LamT('x', $λ__x);
    my $λy_θKy      ::= $λy_λ__y;
    my $λx_θKx      ::= $λx_λ__x;

    my $θI          ::= $λx_x;       #   I aka id
    my $θK          ::= $λx_θKx;     #   K aka const
    my $θB          ::= $LamT('f', $LamT('g', $LamT('x', $AppT($f, $gx))));   #   B aka compose
    my $θC          ::= $LamT('f', $LamT('x', $LamT('y', $fyx)));             #   C aka swap-args

    my $θIk         ::= $AppT($θI, $k);
    my $θIkf1       ::= $AppT($θIk, $f1);
    my $λk_θIkf1    ::= $LamT('k', $θIkf1);

    my $θnil        ::= $LamT('h', $LamT('_', $h));
    my $θcons       ::= $LamT('f1', $LamT('f2', $LamT('_', $LamT('h', $hf1f2))));

    my $θCθcons     ::= $AppT($θC, $θcons);
    my $θCθconsθnil ::= $AppT($θCθcons, $θnil);

    my $out = TestTerms.new({
        'a'                         => $a,
        'b'                         => $b,
        'c'                         => $c,
        'd'                         => $d,
        'e'                         => $e,
        'f'                         => $f,
        'f1'                        => $f1,
        'f2'                        => $f2,
        'f3'                        => $f3,
        'f4'                        => $f4,
        'f5'                        => $f5,
        'g'                         => $g,
        'h'                         => $h,
        'k'                         => $k,

        'u'                         => $u,
        'v'                         => $v,
        'w'                         => $w,
        'x'                         => $x,
        'y'                         => $y,
        'z'                         => $z,
        '"c"'                       => $κc,
        '5'                         => $κ5,

        '(g h)'                     => $gh,
        '(g x)'                     => $gx,
        '(f y)'                     => $fy,

        '(u u)'                     => $uu,
        
        '(x u)'                     => $xu,
        '(x x)'                     => $xx,
        '(x y)'                     => $xy,
        '(x z)'                     => $xz,
        '(x "c")'                   => $xκc,

        '(y u)'                     => $yu,
        '(y x)'                     => $yx,
        '(y y)'                     => $yy,
        '(y z)'                     => $yz,
        '(y "c")'                   => $yκc,

        '(z u)'                     => $zu,
        '(z x)'                     => $zx,
        '(z y)'                     => $zy,
        '(z z)'                     => $zz,
        '(z "c")'                   => $zκc,

        '((f a) b)'                 => $fab,
        '((f b) a)'                 => $fba,
        '((f y) x)'                 => $fyx,
        '((x y) z)'                 => $xyz,
        '((x y) "c")'               => $xyκc,
        '(((x y) z) x)'             => $xyzx,
        '(x (y z))'                 => $AppT($x, $yz),
        '((x (y z)) x)'             => $AppT($AppT($x, $yz), $x),
        '(x (y (z x)))'             => $AppT($x, $AppT($y, $zx)),
        '((x y) (y z))'             => $AppT($xy, $yz),

        '(λ_.x)'                    => $λ__x,
        '(λx."c")'                  => $λx_κc,
        '(λx.x)'                    => $λx_x,   # I aka id
        '(λx.y)'                    => $λx_y,
        '(λx.z)'                    => $λx_z,
        '((λx.x) k)'                => $θIk,
        '(((λx.x) k) f1)'           => $θIkf1,
        '(λk.(((λx.x) k) f1))'      => $λk_θIkf1,
        '(λf.(λg.(λx.(f (g x)))))'  => $θB,
        '(λf.(λx.(λy.((f y) x))))'  => $θC,
        '(λf.(λa.(λb.((f b) a))))'  => $LamT('f', $LamT('a', $LamT('b', $fba))),    # alpha-converted C

        '(λu.(λv.(u u)))'           => $λu_λv_uu,
        '(λu.(λv.(x u)))'           => $λu_λv_xu,
        '(λu.(λv.(y u)))'           => $λu_λv_yu,
        '(λu.(λv.(z u)))'           => $λu_λv_zu,
        '(λw.(λx.(x y)))'           => $λw_λx_xy,
        '(λw.(λx.(x z)))'           => $λw_λx_xz,
        '(λw.(λx.(x (λw.(λx.(x z))))))' => $LamT('w', $LamT('x', $AppT($x, $λw_λx_xz))),
        '(λu.(λv.((λw.(λx.(x y))) u)))' => $LamT('u', $LamT('v', $AppT($λw_λx_xy, $u))),

        '(λx.(λ_.x))'               => $θK,   # K aka const
        '(λx.(x "c"))'              => $λx_xκc,
        '(λx.(x x))'                => $λx_xx,  # omegaX aka ωX ("omega in x") aka ω aka omega
        '(λx.(x y))'                => $λx_xy,
        '(λx.(x z))'                => $λx_xz,
        '(λx.(y x))'                => $λx_yx,
        '(λu.((x y) z))'            => $λu_xyz,
        '(λx.((x y) z))'            => $λx_xyz,
        '(λx.((x y) "c"))'          => $LamT('x', $xyκc),

        '(λ_.y)'                    => $λ__y,
        '(λy.(x x))'                => $λy_xx,
        '(λy.(x y))'                => $λy_xy,
        '(λy.(y y))'                => $λy_yy,   # omegaY aka ωY ("omega in y")
        '(λy.(z y))'                => $λy_zy,
        '(λy.(λ_.y))'               => $λy_θKy,

        '(λg.(λh.((λy.(λ_.y)) (g h))))' => $LamT('g', $LamT('h', $AppT($λy_θKy, $gh))),

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

        '((x y) (λy.(x y)))'        => $AppT($xy, $λy_xy),

        '((λx.(y x)) (x y))'            => $AppT($λx_yx, $xy),
        '(((λx.(y x)) (x y)) x)'        => $AppT($AppT($λx_yx, $xy), $x),
        '(((λx.(y x)) (x y)) (λx.x))'   => $AppT($AppT($λx_yx, $xy), $λx_x),
        '(((λx.(y x)) (λx.x)) (λx.x))'  => $AppT($AppT($λx_yx, $λx_x), $λx_x),

        '((λx.x) x)'                    => $AppT($λx_x, $x),
        '((λx.(y x)) (λy.(x y)))'       => $AppT($λx_yx, $λy_xy),
        '(λx.(x (λy.(x y))))'           => $LamT('x', $AppT($x, $λy_xy)),
        '((λy.(x y)) y)'                => $AppT($λy_xy, $y),
        '(λx.((λy.(z y)) x))'           => $LamT('x', $AppT($λy_zy, $x)),
        '(λx.((λy.(x y)) x))'           => $LamT('x', $AppT($λy_xy, $x)),
        '(λx.((λx.(x y)) x))'           => $LamT('x', $AppT($λx_xy, $x)),
        '((λx.(x x)) (y y))'            => $AppT($λx_xx, $yy),
        '((y y) (λx.(x x)))'            => $AppT($yy, $λx_xx),
        '(x (x y))'                     => $AppT($x, $xy),
        '(x (λy.(x y)))'                => $AppT($VarT("x"), $λy_xy),

        '(λx.((λy.(z y)) (x x)))'       => $LamT("x", $AppT($λy_zy, $xx)),
        '(λz.(x (x y)))'                => $LamT('z', $AppT($x, $xy)),
        '(λz.(x (λy.(x y))))'           => $LamT("z", $AppT($VarT("x"), $λy_xy)),

        '((λx.(x x)) (λx.(x x)))'       => $AppT($λx_xx, $λx_xx), # = (ωX ωX) aka ΩXX ("Omega in x") aka Ω aka Omega
        '((λy.(y y)) (λy.(y y)))'       => $AppT($λy_yy, $λy_yy), # = (ωY ωY) aka ΩYY ("Omega in y")
        '((λx.(x x)) (λy.(y y)))'       => $AppT($λx_xx, $λy_yy), # = (ωX ωY) aka ΩXY (same as Ω modulo α-conversion)
        '((λy.(y y)) (λx.(x x)))'       => $AppT($λy_yy, $λx_xx), # = (ωY ωX) aka ΩYX (same as Ω modulo α-conversion)
        '((λx.(x x)) (λy.(x x)))'       => $AppT($λx_xx, $λy_xx), # NOT Ω (wrong binder in 2nd λ)
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
        .aka('(u u)', 'u u')\
        .aka('(x u)', 'x u')\
        .aka('(x x)', 'x x')\
        .aka('(y u)', 'y u')\
        .aka('(z u)', 'z u')\
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
        .aka('(λx.y)', 'λx.y')\
        .aka('(λx.z)', 'λx.z')\
        .aka('((λx.x) k)', '(λx.x) k')\
        .aka('(((λx.x) k) f1)', '((λx.x) k) f1', '(λx.x) k f1')\
        .aka('(λk.(((λx.x) k) f1))', 'λk.(((λx.x) k) f1)', 'λk.(λx.x) k f1')\
        .aka('(λx.(λ_.x))', 'K', 'const', 'λx.(λ_.x)', 'λx.λ_.x')\
        .aka('(λy.(λ_.y))', 'λy.(λ_.y)', 'λy.λ_.y')\
        .aka('(λg.(λh.((λy.(λ_.y)) (g h))))', 'λg.(λh.((λy.(λ_.y)) (g h)))', 'λg.λh.(λy.λ_.y) (g h)')\
        .aka('(λx.(x "c"))', 'λx.(x "c")', 'λx.x "c"')\
        .aka('(λx.(x x))', 'ωX', 'omegaX', 'ω', 'omega', 'λx.(x x)', 'λx.x x')\
        .aka('(λx.(x y))', 'λx.(x y)', 'λx.x y')\
        .aka('(λx.(x z))', 'λx.(x z)', 'λx.x z')\
        .aka('(λx.(y x))', 'λx.(y x)', 'λx.y x')\
        .aka('(λu.((x y) z))', 'λu.((x y) z)', 'λu.x y z', '(λu.x y z)')\
        .aka('(λx.((x y) z))', 'λx.((x y) z)', 'λx.x y z', '(λx.x y z)')\
        .aka('(λx.((x y) "c"))', 'λx.((x y) "c")', 'λx.x y "c"', '(λx.x y "c")')\
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

        .aka('(λu.(λv.(u u)))', 'λu.(λv.(u u))', 'λu.λv.u u', '(λu.λv.u u)')\
        .aka('(λu.(λv.(x u)))', 'λu.(λv.(x u))', 'λu.λv.x u', '(λu.λv.x u)')\
        .aka('(λu.(λv.(y u)))', 'λu.(λv.(y u))', 'λu.λv.y u', '(λu.λv.y u)')\
        .aka('(λu.(λv.(z u)))', 'λu.(λv.(z u))', 'λu.λv.z u', '(λu.λv.z u)')\
        .aka('(λw.(λx.(x y)))', 'λw.(λx.(x y))', 'λw.λx.x y', '(λw.λx.x y)')\
        .aka('(λw.(λx.(x z)))', 'λw.(λx.(x z))', 'λw.λx.x z', '(λw.λx.x z)')\
        .aka('(λw.(λx.(x (λw.(λx.(x z))))))', 'λw.(λx.(x (λw.(λx.(x z)))))', 'λw.λx.x λw.λx.x z', '(λw.λx.x λw.λx.x z)', 'λw.λx.x (λw.λx.x z)', '(λw.λx.x (λw.λx.x z))')\
        .aka('(λu.(λv.((λw.(λx.(x y))) u)))', 'λu.(λv.((λw.(λx.(x y))) u))', 'λu.λv.(λw.λx.x y) u', '(λu.λv.(λw.λx.x y) u)', 'λu.λv.((λw.λx.x y) u)', '(λu.λv.((λw.λx.x y) u))')\

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

    $out.constructionTime = now.Real - $time.Real;

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

sub testTermFn($f, 
    :$argToStr = -> $a { $a ~~ Str ?? $a.perl !! $a.Str }, 
    :$expectedToStr, 
    *@tests
) is export {
    my Str $fgist = $f.gist;
    subtest({
        for @tests -> $test {
            my Any   $args = $test.key;
            my @args;
            my @argStrs;

            if $args ~~ Str {
                @args    = `$args;
            } elsif $args ~~ TTerm {
                @args    = $args;
            } elsif $args ~~ Array {
                @args = $args.list.map(&convert2Lambda);
            } else {
                die "expected either a TTerm or a Str or an Array but got {$args.perl}";
            }

            my Str   $argStr        = @args.map($argToStr).join(' ');
            my Any   $expected      = &convert2Lambda($test.value);
            my Str   $expectedStr   = $expectedToStr.defined
                                        ?? ' -> ' ~ $expectedToStr($expected)
                                        !! '';
            my $desc = "($fgist $argStr)$expectedStr";

            is($f(|@args), $expected, $desc);
        }
    }, "$fgist on various inputs");
}

my sub fail_eq-Term(Str:D $msg, TTerm:D $actual, TTerm:D $expected, Bool :$full = False) {
    my $t2src = ($full ?? $Term2srcLess !! $Term2srcFull);
    my $actualSrc = $t2src($actual);
    my $actualStr = $actual.Str;
    my $expectedSrc = $t2src($expected);
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
        fail_eq-Term($m, $actual, $expected, :$full);
    }
}
