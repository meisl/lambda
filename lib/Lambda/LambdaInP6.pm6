use v6;

use Lambda::TermADT;


class Env is export {
    has Env $!parent;
    has     %!bindings = %();

    submethod BUILD(:$!parent, :%!bindings) {
        for %!bindings.pairs -> $pair {
            my $k = $pair.key;
            my $v = $pair.value;
            die "expected TTerm value in binding of $k but got {$v.perl}"
                unless $v ~~ TTerm && $v.defined;
        }
    }

    my $emptyEnv = Env.new(:parent(Env)) does role {
        method lookup(Str:D $name) {
            die "unbound: $name";
        }
    }

    method empty(Env:U:) returns Env:D { $emptyEnv }

    method lookup(Env:D: Str:D $name) {
        %!bindings{$name} // $!parent.lookup($name);
    }

    multi method extend(Env:D: *%bindings) returns Env:D {
        die "must add at least one binding when extending an Env"
            unless %bindings.elems > 0;
        self.extend(%bindings);
    }

    multi method extend(Env:D: %bindings) returns Env:D {
        Env.new(:parent(self), :%bindings);
    }
}


class TermStub is export {
    has Callable:D $!f;

    method new(Callable:D $f) {
        self.bless(:$f);
    }

    submethod BUILD(:$!f) {
    }

    method in(TermStub:D: Env:D $env) returns TTerm {
        $!f.($env);
    }
}

multi sub app(@xs) returns TermStub {
    return TermStub.new(-> Env:D $env {
        #say "app $depth: {@xs.perl}";
        my @ts = @xs.tree.map(-> $x {
            if $x ~~ Str {
                $env.lookup($x) // die "unbound symbol $x in ({@xs})";
            } elsif $x ~~ TTerm {
                $x
            } elsif $x ~~ TermStub {
                $x.in($env)
            } elsif $x ~~ Positional {
                app($x).in($env)
            } else {
                die "can `app` Str or or TermStub or TTerm but not $x|{$x.WHICH}";
            }
        });
        #say "app $depth / got: [{@ts.map(*.lambda).join(', ')}]";
        if @ts == 0 {
            die "empty application!";
        } elsif @ts == 1 {
            @ts[0];
        } else {
            @ts.reduce(-> TTerm:D $a, TTerm $b { 
                $AppT($a, $b)
            });
        }
    });
}

multi sub app(Str:D $x) returns TermStub {
    app([$x]);
}


my $env = Env.empty.extend(:x($VarT('foo')));
say $Term2source( app(<x>).in($env) );
say $Term2source( app(<x x>).in($env) );
say $Term2source( app(<x y>).in($env.extend(:y($VarT('bar')))) );
say $Term2source( app((<x>, <y z>)).in($env.extend(:y($VarT('bar')), :z($VarT('baz')))) );
say '';


my multi sub lam(@vs, @body) returns TermStub {
    die "need at least 1 var for lam"
        unless @vs > 0;
    my @vNms = @vs.map({
        $_ ~~ Str 
            ?? $_
            !! $VarT2name($_)
    });
    my @vars = @vNms.map($VarT);
    my %bindings = @vNms Z @vars;
    return TermStub.new(-> Env:D $env {
        my $body = app(@body).in($env.extend(%bindings));
        my TTerm $out = ($body, @vars.reverse).reduce(-> $b, $v {$LamT($v, $b)});

        if False {
            #say 'env: [' ~ %env.map(-> $pair {$pair.key ~ ' => ' ~ $pair.value.lambda}).join(', ') ~ ']';
            say 'vars: ' ~ @vNms.map(*.perl);
            say 'body: ' ~ $Term2source($body);
            say 'all: ' ~ $Term2source($out);
            say '';
        }

        $out;
    });
}

my multi sub lam(@vs, $body) returns TermStub {
    lam(@vs, [$body]);
}

my multi sub lam($vs, $body) returns TermStub {
    lam([$vs], [$body]);
}

$env = Env.empty.extend(:x($VarT('foo')), :y($VarT('bar')));

say $Term2source( lam(<x>, <x>).in($env) );
say $Term2source( lam(<x>, <x x>).in($env) );
say $Term2source( lam(<x y>, <x>).in($env) );
say $Term2source( lam(<x y>, <x y>).in($env) );
say $Term2source( lam(<x y u>, <x y>).in($env) );
say $Term2source( lam(<x>, <x y>).in($env) );
say $Term2source( lam(<x y z>, <x y z>).in($env) );
say $Term2source( lam(<x y z>, (<x>, <y z>)).in($env) );
say '';

$env = $env.extend(:id(lam(<x>, <x>).in(Env.empty)));
say $Term2source( lam(<x>, <id>).in($env) );
say '';


multi sub let(%decls, $body) returns TermStub {
    my @names = %decls.keys.reverse;
    #my $lam = lam(@names, $body);
    #my $out = app([$lam, %decls.values.reverse]);

    my $out = ($body, @names).reduce(-> $t, $name {
        app([lam($name, $t), %decls{$name}])
    });
    $out;
}

say $Term2source( let(
    { id        => 'id',
      fst       => lam(<x y>, <x>),
      snd       => lam(<x y>, <y>),
      K         => 'fst',
      '#true'   => 'fst',
      '#false'  => 'snd',
      'not'     => lam(<p>, <p #false #true>),
    },
    <K id>
    ).in(Env.empty.extend(:id(lam(<x>, <x>).in(Env.empty))))
);



#((λK.λid.K id) (λx.λy.x)) (λx.x)

#(λid.(λK.K id) (λx.λy.x)) (λx.x)


#((λid.λK.(K id)) (λx.(λy.((λx.x) x)))) (λx.x)

#constant $not is export = lambdaFn(
#    'not', 'λp.p #false #true',
#    -> TBool:D $p { $p($false, $true) }
#);
