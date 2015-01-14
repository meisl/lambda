use v6;
use Test;
use Test::Util;

use Lambda::TermADT;
use Lambda::Boolean;


# module under test:
use Lambda::LambdaInP6;

plan 54;


# TermStub (basic)
{
    dies_ok({ TermStub.new() }, 'cannot call TermStub.new with no args');
    dies_ok({ TermStub.new(Callable) }, 'cannot call TermStub.new with undef Callable');
    
    my $x = $VarT('x');
    my $s1 = TermStub.new(-> Env:D $env { $LamT($x, $x) });
    isa_ok $s1, TermStub, 'can call TermStub.new with fn Env:D -> TTerm';
}


# Env(ironment)
{
    my $e = Env.empty;
    isa_ok $e, Env, 'Env.empty is an Env';
    cmp_ok $e, '===', Env.empty, 'Env.empty always returns the same thing';
    
    dies_ok({ $e.empty }, 'cannot call .empty on Env instance');
    dies_ok({ Env.lookup }, 'cannot call .lookup on Env class');
    dies_ok({ Env.extend }, 'cannot call .extend on Env class');

    dies_ok({ $e.extend() }, '.extend (on instance) needs at least one binding');
    dies_ok({ $e.extend(:foo('foo')) }, 'cannot .extend with named arg bound to Str');
    dies_ok({ $e.extend(:foo(TTerm)) }, 'cannot .extend with named arg bound to undef TTerm');
    dies_ok({ $e.extend(:foo(TermStub)) }, 'cannot .extend with named arg bound to undef TermStub');
    dies_ok({ $e.extend(:foo(TermStub.new(-> Env:D $env {} ))) }, 'cannot .extend with named arg bound to TermStub instance');

    dies_ok({ $e.extend( %(foo => 'foo') ) }, 'cannot .extend with Str => Str in hash');
    dies_ok({ $e.extend( %(foo => TTerm) ) }, 'cannot .extend with Str => undef TTerm in hash');
    dies_ok({ $e.extend( %(foo => TermStub) ) }, 'cannot .extend with Str => undef TermStub in a hash');
    dies_ok({ $e.extend( %(foo => TermStub.new(-> Env:D $env {} )) ) }, 'cannot .extend with Str => TermStub instance in a hash');

    my $x = $VarT('x');
    my Env:D $e2;
    
    lives_ok({ $e2 = $e.extend(:foo($x)) }, 'can .extend with named arg bound to a TTerm');
    isa_ok $e2, Env, '.extend with named arg bound to a TTerm returns an Env';
    is $e2 === $e, False, '.extend with named arg bound to a TTerm returns a *different* Env';

    cmp_ok $e2.lookup('foo'), '===', $x, 'can look up in env extended with named arg bound to a TTerm';
    
    lives_ok({ $e2 = $e.extend(%(foo => $x)) }, 'can .extend with Str => TTerm in a hash');
    isa_ok $e2, Env, '.extend with Str => TTerm in a hash returns an Env';
    is $e2 === $e, False, '.extend with Str => TTerm in a hash returns a *different* Env';

    cmp_ok $e2.lookup('foo'), '===', $x, 'can look up in env extended with Str => TTerm in a hash';

    my $y = $VarT('y');
    my Env:D $e3 = $e2.extend(:bar($y));
    cmp_ok $e3.lookup('bar'), '===', $y, 'direct look up in child env';
    cmp_ok $e3.lookup('foo'), '===', $x, 'indirect look up in child env (from parent env)';

    my $z = $VarT('z');
    my Env:D $e4 = $e3.extend(:bar($z));
    cmp_ok $e4.lookup('bar'), '===', $z, 'direct look up in child env / hiding parent\'s binding';
    cmp_ok $e3.lookup('bar'), '===', $y, '...but parent env still holds the old binding';
    cmp_ok $e4.lookup('foo'), '===', $x, 'indirect look up in child env (from parent of parent env)';

}


# TermStub.in(Env)
{
    my $x = $VarT('x');
    my $t = $LamT($x, $x);
    my @seen = @();
    my &f = -> Env:D $env { @seen.push($env); $t };
    my $s1 = TermStub.new(&f);

    dies_ok({ $s1.in(Env) }, 'cannot call .in on TermStub instance with undef Env');

    my $e = Env.empty;
    cmp_ok($s1.in($e), '===', $t, 'calling .in on TermStub.new(&f) yields what &f returns');
    is @seen.elems, 1, '.in called &f once';
    cmp_ok(@seen[0], '===', $e, '.in passed the Env to &f');
}


# app
{
    my $x = $VarT('x');
    my $y = $VarT('y');
    my $z = $VarT('z');
    my $e1 = Env.empty.extend(:x($x));
    my $e2 = $e1.extend(:y($y));
    my $e3 = $e2.extend(:z($z));
    my $t;
    
    $t = app(<x>).in($e1);
    cmp_ok($t, '===', $x, 'app(<x>).in(..) yields VarT');
    
    $t = app(<x x>).in($e1);
    cmp_ok($AppT2func($t), '===', $x, 'app(<x x>).in(..) yields AppT with func = var x');
    cmp_ok($AppT2arg($t), '===', $x, 'app(<x x>).in(..) yields AppT with arg = var x');
    
    $t = app(<x y>).in($e2);
    cmp_ok($AppT2func($t), '===', $x, 'app(<x y>).in(..) yields AppT with func = var x');
    cmp_ok($AppT2arg($t), '===', $y, 'app(<x y>).in(..) yields AppT with arg = var y');
    
    $t = app((<x>, <y z>)).in($e3);
    cmp_ok($AppT2func($t), '===', $x, 'app((<x> <y z>)).in(..) yields AppT with func = var x');
    cmp_ok($AppT2func($AppT2arg($t)), '===', $y, 'app((<x> <y z>)).in(..) yields AppT with arg = (AppT y z)');
    cmp_ok($AppT2arg($AppT2arg($t)), '===', $z, 'app((<x> <y z>)).in(..) yields AppT with arg = (AppT y z)');
}


# lam
{
    my $x = $VarT('x');
    my $y = $VarT('y');
    my $z = $VarT('z');
    my $env0 = Env.empty;
    my $env1 = $env0.extend(:x($x), :y($y));
    my $t;

    $t = lam(<x>, <x>).in($env0);
    cmp_ok($LamT2var($t), '===', $x, 'lam(<x>, <x>) yields LamT with var = var x');
    cmp_ok($LamT2body($t), '===', $x, 'lam(<x>, <x>) yields LamT with body = var x');

    $t = lam(<x>, <x x>).in($env0);
    cmp_ok($LamT2var($t), '===', $x, 'lam(<x>, <x x>) yields LamT with var = var x');
    cmp_ok($AppT2func($LamT2body($t)), '===', $x, 'lam(<x>, <x x>) yields LamT with body = (AppT x x)');
    cmp_ok($AppT2arg($LamT2body($t)), '===', $x, 'lam(<x>, <x x>) yields LamT with body = (AppT x x)');

    $t = lam(<x y>, <x>).in($env0);
    cmp_ok($LamT2var($t), '===', $x, 'lam(<x y>, <x>) yields LamT with var = var x');
    cmp_ok($LamT2var($LamT2body($t)), '===', $y, 'lam(<x y>, <x>) yields LamT with body = (LamT y x)');
    cmp_ok($LamT2body($LamT2body($t)), '===', $x, 'lam(<x y>, <x>) yields LamT with body = (LamT y x)');

    $t = lam(<x y>, <y x>).in($env0);
    cmp_ok($LamT2var($t), '===', $x, 'lam(<x y>, <x>) yields LamT with var = var x');
    cmp_ok($LamT2var($LamT2body($t)), '===', $y, 'lam(<x y>, <y x>) yields LamT with body = (LamT y (AppT y x))');
    cmp_ok($AppT2func($LamT2body($LamT2body($t))), '===', $y, 'lam(<x y>, <y x>) yields LamT with body = (LamT y (AppT y x))');
    cmp_ok($AppT2arg($LamT2body($LamT2body($t))), '===', $x, 'lam(<x y>, <y x>) yields LamT with body = (LamT y (AppT y x))');
}