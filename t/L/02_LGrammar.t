#!nqp
use testing;
use Util;

use L::LGrammar;


plan(26);

{
    my $m;

    dies_ok( { $m := LGrammar.parse('') }, 'empty string');
    dies_ok( { $m := LGrammar.parse('    ') },       'only white space (a)');
    dies_ok( { $m := LGrammar.parse("    \n  ") },   'only white space (b)');
    dies_ok( { $m := LGrammar.parse("   # comment\n  ") },   'only eol-comment and white space');

#!?    dies_ok( { $m := LGrammar.parse('(x y') }, 'unbalanced open paren')
#!?        || diag('.orig: ' ~ describe($m.orig) ~  ', .from: ' ~ $m.from ~  ', .to: ' ~ $m.to ~  ', .chars: ' ~ $m.chars);

#!?    dies_ok( { $m := LGrammar.parse('(x y))') }, 'unbalanced close paren')
#!?        || diag('.orig: ' ~ describe($m.orig) ~  ', .from: ' ~ $m.from ~  ', .to: ' ~ $m.to ~  ', .chars: ' ~ $m.chars);


#!?    dies_ok( { $m := LGrammar.parse('()') }, 'open and close parens')
#!?        || diag('.orig: ' ~ describe($m.orig) ~  ', .from: ' ~ $m.from ~  ', .to: ' ~ $m.to ~  ', .chars: ' ~ $m.chars);

    dies_ok({ $m := LGrammar.parse('7') }, 'a digit')
        || diag('.orig: ' ~ describe($m.orig) ~  ', .from: ' ~ $m.from ~  ', .to: ' ~ $m.to ~  ', .chars: ' ~ $m.chars);

    lives_ok({ $m := LGrammar.parse('x') }, 'one var name');
#!?    dies_ok( { $m := LGrammar.parse('(x)') }, 'one var name with parens on the outside')
#!?        || diag('.orig: ' ~ describe($m.orig) ~  ', .from: ' ~ $m.from ~  ', .to: ' ~ $m.to ~  ', .chars: ' ~ $m.chars);
    lives_ok({ $m := LGrammar.parse('x y') }, 'two var names');
    lives_ok({ $m := LGrammar.parse('x y') }, 'two var names with parens on the outside');
    lives_ok({ $m := LGrammar.parse('x y x') }, 'three var names');

    lives_ok({ $m := LGrammar.parse('x (y x)') }, 'three var names with parens');


    lives_ok({ $m := LGrammar.parse('λx.x x') }, 'a lambda');
    lives_ok({ $m := LGrammar.parse('(λx.x x)') }, 'a lambda with parens on the outside');
    lives_ok({ $m := LGrammar.parse('λx.(x x)') }, 'a lambda with parens around body');
    lives_ok({ $m := LGrammar.parse('(λx.(x x))') }, 'a lambda with parens around body and on the outside');

    lives_ok({ $m := LGrammar.parse('""') }, 'empty string literal');
    lives_ok({ $m := LGrammar.parse('"foo"') }, 'string literal');
    is(~LGrammar.parse('"foo\nbar"'), '"foo\nbar"', 'string literal with escape seq \n');
    dies_ok({ $m := LGrammar.parse('"foo\v"') }, 'string literal with invalid escape seq \v');

}


{ # simple let ----------------------------------------------------------------
    my $m;
    dies_ok({ $m := LGrammar.parse('(δ((K λx.λ_.x)) K K)') }, 'simple let with no ws after δ');
    lives_ok({$m := LGrammar.parse("(δ# comment til end of line\n((K λx.λ_.x)) K K)") }, 'simple let with no ws after δ (eol-comment)');
    is(~$m, "(δ# comment til end of line\n((K λx.λ_.x)) K K)", 'simple let with no ws after δ (eol-comment) / match');

    lives_ok({$m := LGrammar.parse('(δ ((K λx.λ_.x)) K K)') }, 'simple let with one binding');
    is(~$m, '(δ ((K λx.λ_.x)) K K)', 'simple let with one binding / match');
    dies_ok({ $m := LGrammar.parse('(δ ((λ λx.λ_.x)) K K)') }, 'simple let with invalid binder');

    lives_ok({$m := LGrammar.parse('(delta ((I λx.x)) I I)') }, 'simple let with "delta" instead of δ');
    is(~$m, '(delta ((I λx.x)) I I)', 'simple let with "delta" instead of δ / match');
}


done();
