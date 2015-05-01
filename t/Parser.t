use v6;
use Test;
use Test::Util;
use Test::Util_Lambda;

use Lambda::Boolean;
use Lambda::String;
use Lambda::PairADT;
use Lambda::MaybeADT;
use Lambda::ListADT;


use Lambda::Conversion;


# module(s) under test:
use Lambda::Parser;

plan 20;


# test helpers ----------------------------------------------------------------


sub is_Some($maybe, $expectedValue, Str $msg?) {
    my $expected = $Some(convert2Lambda($expectedValue));
    case-Maybe($maybe,
        None => { ok(False, $msg // "") or diag("expected $expected but got None") and False },
        Some => -> $v {
            is "(Some $v)", $expected, $msg;  # TODO: improve msg
        }
    )
}

sub is_None($maybe, Str $msg?) {
    case-Maybe($maybe,
        None => { ok(True, $msg) },
        Some => -> $v { ok(False, $msg // "") or diag("expected a None but got (Some " ~ $v ~ ")") and False }
    )
}


# -----------------------------------------------------------------------------


subtest({ # str_P
    is_properLambdaFn($str_P, 'str_P');
    
    my $s = 'some string';
    
    diag '(str_P ""):    ' ~ $str_P('');
    diag '(str_P "f"):   ' ~ $str_P('f');
    diag '(str_P "fo"):  ' ~ $str_P('fo');
    diag '(str_P "foo"): ' ~ $str_P('foo');

    is_None($str_P('foo')($s),                                      "(str_P 'foo' {$s.perl})  ~> None");
    is_Some($str_P('')($s),             $Pair('', 'some string'),   "(str_P '' {$s.perl})");
    is_Some($str_P('s')($s),            $Pair('s', 'ome string'),   "(str_P 's' {$s.perl})");
    is_Some($str_P('so')($s),           $Pair('so', 'me string'),   "(str_P 'so' {$s.perl})");
    is_Some($str_P('som')($s),          $Pair('som', 'e string'),   "(str_P 'som' {$s.perl})");
    is_Some($str_P('some')($s),         $Pair('some', ' string'),   "(str_P 'some' {$s.perl})");
    is_Some($str_P('some ')($s),        $Pair('some ', 'string'),   "(str_P 'some ' {$s.perl})");
    is_Some($str_P($s)($s),             $Pair($s, ''),              "(str_P '$s' {$s.perl})");
    is_None($str_P($s ~ 'XXX')($s),                                 "(str_P '{$s}XXX' {$s.perl})  ~>  None");

    $s = 'here is a rather long string, so we can estimate performance';
    my $p       = diagTime { $str_P($s) },  'big str parser construction';
    my $actual  = diagTime { $p($s) },      'big str parser application';
    is_Some($actual,            $Pair($s, ''),      "(str_P '$s' {$s.perl})");

    $p = $str_P($s);
    is_Some($p($s ~ 'XXX'),     $Pair($s, 'XXX'),   "(str_P '$s' {($s ~ 'XXX').perl})");

    $p = $str_P($s ~ 'XXX');
    is_None($p($s),                                 "(str_P '{$s}XXX' {$s.perl})  ~>  None");
}, 'string_P');


subtest({ # oneOrZero_P
    is_properLambdaFn($oneOrZero_P, 'oneOrZero_P');
    
    my $oneOrZero-as = $oneOrZero_P($chr_P('a'));

    is_Some($oneOrZero-as(''),   $Pair([],      ''),    '(oneOrZero_P (chr_P "a") "")');
    is_Some($oneOrZero-as('a'),  $Pair(['a'],   ''),    '(oneOrZero_P (chr_P "a") "a")');
    is_Some($oneOrZero-as('aa'), $Pair(['a'],   'a'),   '(oneOrZero_P (chr_P "a") "aa")');

    is_Some($oneOrZero-as('b'),   $Pair([],     'b'),   '(oneOrZero_P (chr_P "a") "b")');
    is_Some($oneOrZero-as('ab'),  $Pair(['a'],  'b'),   '(oneOrZero_P (chr_P "a") "ab")');
    is_Some($oneOrZero-as('aab'), $Pair(['a'],  'ab'),  '(oneOrZero_P (chr_P "a") "aab")');
}, 'oneOrZero_P');


# many_P-foldl & many_P-foldr -------------------------------------------------

subtest({ # many_P-foldl
    is_properLambdaFn($many_P-foldl, 'many_P-foldl');
    
    my $parse = $many_P-foldl(-> $a, $b { "($a $b)" }, '', $nxt_P);
    
    is_Some($parse(''),     $Pair('', ''),              '((many_P-foldl (λa.λb."(" ~ a ~ " " ~ b ~ ")") "" nxt_P) "")');
    is_Some($parse('a'),    $Pair('( a)', ''),          '((many_P-foldl (λa.λb."(" ~ a ~ " " ~ b ~ ")") "" nxt_P) "a")');
    is_Some($parse('ab'),   $Pair('(( a) b)', ''),      '((many_P-foldl (λa.λb."(" ~ a ~ " " ~ b ~ ")") "" nxt_P) "ab")');
    is_Some($parse('abc'),  $Pair('((( a) b) c)', ''),  '((many_P-foldl (λa.λb."(" ~ a ~ " " ~ b ~ ")") "" nxt_P) "abc")');
}, 'many_P-foldl');

subtest({ # many_P-foldr
    is_properLambdaFn($many_P-foldr, 'many_P-foldr');
    
    my $parse = $many_P-foldr(-> $a, $b { "($a $b)" }, '', $nxt_P);
    
    is_Some($parse(''),     $Pair('', ''),              '((many_P-foldr (λa.λb."(" ~ a ~ " " ~ b ~ ")") "" nxt_P) "")');
    is_Some($parse('a'),    $Pair('(a )', ''),          '((many_P-foldr (λa.λb."(" ~ a ~ " " ~ b ~ ")") "" nxt_P) "a")');
    is_Some($parse('ab'),   $Pair('(a (b ))', ''),      '((many_P-foldr (λa.λb."(" ~ a ~ " " ~ b ~ ")") "" nxt_P) "ab")');
    is_Some($parse('abc'),  $Pair('(a (b (c )))', ''),  '((many_P-foldr (λa.λb."(" ~ a ~ " " ~ b ~ ")") "" nxt_P) "abc")');
}, 'many_P-foldr');


# many1_P-foldl & many1_P-foldr -----------------------------------------------

subtest({ # many1_P-foldl
    is_properLambdaFn($many1_P-foldl, 'many1_P-foldl');
    
    my $parse = $many1_P-foldl(-> $a, $b { "($a $b)" }, '', $nxt_P);
    
    is_None($parse(''),                                 '((many1_P-foldl (λa.λb."(" ~ a ~ " " ~ b ~ ")") "" nxt_P) "")  ~>  None');
    is_Some($parse('a'),    $Pair('( a)', ''),          '((many1_P-foldl (λa.λb."(" ~ a ~ " " ~ b ~ ")") "" nxt_P) "a")');
    is_Some($parse('ab'),   $Pair('(( a) b)', ''),      '((many1_P-foldl (λa.λb."(" ~ a ~ " " ~ b ~ ")") "" nxt_P) "ab")');
    is_Some($parse('abc'),  $Pair('((( a) b) c)', ''),  '((many1_P-foldl (λa.λb."(" ~ a ~ " " ~ b ~ ")") "" nxt_P) "abc")');
}, 'many1_P-foldl');

subtest({ # many1_P-foldr
    is_properLambdaFn($many1_P-foldr, 'many1_P-foldr');
    
    my $parse = $many1_P-foldr(-> $a, $b { "($a $b)" }, '', $nxt_P);
    
    is_None($parse(''),                                 '((many1_P-foldr (λa.λb."(" ~ a ~ " " ~ b ~ ")") "" nxt_P) "")  ~>  None');
    is_Some($parse('a'),    $Pair('(a )', ''),          '((many1_P-foldr (λa.λb."(" ~ a ~ " " ~ b ~ ")") "" nxt_P) "a")');
    is_Some($parse('ab'),   $Pair('(a (b ))', ''),      '((many1_P-foldr (λa.λb."(" ~ a ~ " " ~ b ~ ")") "" nxt_P) "ab")');
    is_Some($parse('abc'),  $Pair('(a (b (c )))', ''),  '((many1_P-foldr (λa.λb."(" ~ a ~ " " ~ b ~ ")") "" nxt_P) "abc")');
}, 'many1_P-foldr');


# many1_P-foldl1 & many1_P-foldr1 ---------------------------------------------

subtest({ # many1_P-foldl1
    is_properLambdaFn($many1_P-foldl1, 'many1_P-foldl1');
    
    my $parse = $many1_P-foldl1(-> $a, $b { "($a $b)" }, $nxt_P);
    
    is_None($parse(''),                             '((many1_P-foldl1 (λa.λb."(" ~ a ~ " " ~ b ~ ")") nxt_P) "")');
    is_Some($parse('a'),    $Pair('a', ''),         '((many1_P-foldl1 (λa.λb."(" ~ a ~ " " ~ b ~ ")") nxt_P) "a")');
    is_Some($parse('ab'),   $Pair('(a b)', ''),     '((many1_P-foldl1 (λa.λb."(" ~ a ~ " " ~ b ~ ")") nxt_P) "ab")');
    is_Some($parse('abc'),  $Pair('((a b) c)', ''), '((many1_P-foldl1 (λa.λb."(" ~ a ~ " " ~ b ~ ")") nxt_P) "abc")');
}, 'many1_P-foldl1');

subtest({ # many1_P-foldr1
    is_properLambdaFn($many1_P-foldr1, 'many1_P-foldr1');
    
    my $parse = $many1_P-foldr1(-> $a, $b { "($a $b)" }, $nxt_P);
    
    is_None($parse(''),                             '((many1_P-foldr1 (λa.λb."(" ~ a ~ " " ~ b ~ ")") nxt_P) "")');
    is_Some($parse('a'),    $Pair('a', ''),         '((many1_P-foldr1 (λa.λb."(" ~ a ~ " " ~ b ~ ")") nxt_P) "a")');
    is_Some($parse('ab'),   $Pair('(a b)', ''),     '((many1_P-foldr1 (λa.λb."(" ~ a ~ " " ~ b ~ ")") nxt_P) "ab")');
    is_Some($parse('abc'),  $Pair('(a (b c))', ''), '((many1_P-foldr1 (λa.λb."(" ~ a ~ " " ~ b ~ ")") nxt_P) "abc")');
}, 'many1_P-foldr1');


subtest({ # noneOf_P
    is_properLambdaFn($noneOf_P, 'noneOf_P');

    my $p;

    dies_ok { $noneOf_P("") }, '(noneOf_P "") dies';

    $p = $noneOf_P("abc");
    is_None $p(""),                     '(noneOf_P "abc" "")  ~> None';
    is_Some $p("x"),  $Pair('x', ''),   '(noneOf_P "abc" "x")';
    is_Some $p("xa"), $Pair('x', 'a'),  '(noneOf_P "abc" "xa")';

    is_None $p("abc"),                  '(noneOf_P "abc" "abc")  ~> None';
    is_None $p("bca"),                  '(noneOf_P "abc" "bca")  ~> None';
    is_None $p("cab"),                  '(noneOf_P "abc" "cba")  ~> None';
}, 'noneOf_P');

subtest({ # anyOf_P
    is_properLambdaFn($anyOf_P, 'anyOf_P');

    my $p;

    dies_ok { $anyOf_P("") }, '(anyOf_P "") dies';

    $p = $anyOf_P("abc");
    is_None $p(""),                     '(anyOf_P "abc" "")  ~> None';
    is_None $p("x"),                    '(anyOf_P "abc" "x")  ~> None';
    is_None $p("xa"),                   '(anyOf_P "abc" "xa")  ~> None';

    is_Some $p("abc"), $Pair('a', 'bc'), '(anyOf_P "abc" "abc")';
    is_Some $p("bca"), $Pair('b', 'ca'), '(anyOf_P "abc" "bca")';
    is_Some $p("cab"), $Pair('c', 'ab'), '(anyOf_P "abc" "cba")';
}, 'anyOf_P');


subtest({ # linebreak_P
    is_properLambdaFn($linebreak_P, 'linebreak_P');

    is_None $linebreak_P(""),                                   '(linebreak_P "")';
    is_None $linebreak_P("foo"),                                '(linebreak_P "foo")';

    is_Some $linebreak_P("\n"),         $Pair("\n", ""),        '(linebreak_P "\n")';
    is_Some $linebreak_P("\nfoo"),      $Pair("\n", "foo"),     '(linebreak_P "\nfoo")';

    is_Some $linebreak_P("\r"),         $Pair("\r", ""),        '(linebreak_P "\r")';
    is_Some $linebreak_P("\rfoo"),      $Pair("\r", "foo"),     '(linebreak_P "\rfoo")';

    is_Some $linebreak_P("\n\n"),       $Pair("\n", "\n"),      '(linebreak_P "\n\n")';
    is_Some $linebreak_P("\n\nfoo"),    $Pair("\n", "\nfoo"),   '(linebreak_P "\n\nfoo")';

    is_Some $linebreak_P("\n\r"),       $Pair("\n", "\r"),      '(linebreak_P "\n\r")';
    is_Some $linebreak_P("\n\rfoo"),    $Pair("\n", "\rfoo"),   '(linebreak_P "\n\rfoo")';

    is_Some $linebreak_P("\r\n"),       $Pair("\r\n", ""),      '(linebreak_P "\r\n")';
    is_Some $linebreak_P("\r\nfoo"),    $Pair("\r\n", "foo"),   '(linebreak_P "\r\nfoo")';
}, 'linebreak_P');


# -----------------------------------------------------------------------------

subtest({ # return_P
    is_properLambdaFn($return_P, 'return_P');

    is_Some $return_P(23, ''),              $Pair(23, ''),              '(return_P 23 "")';
    is_Some $return_P('baz', 'foo-bar'),    $Pair('baz', 'foo-bar'),    '(return_P "baz" "foo-bar")';
}, 'return_P');

subtest({ # fail_P
    is_properLambdaFn($fail_P, 'fail_P');
    
    is_None $fail_P(''),        '(fail_P "") ~> None';
    is_None $fail_P('foo-bar'), '(fail_P "foo-bar") ~> None';
}, 'fail_P');

subtest({ # nxt_P
    is_properLambdaFn($nxt_P, 'nxt_P');
    
    is_None $nxt_P(''),                         '(nxt_P "") ~> None';
    is_Some $nxt_P('x'),    $Pair('x', ''),     '(nxt_P "x")';
    is_Some $nxt_P('xyz'),  $Pair('x', 'yz'),   '(nxt_P "xyz")';
}, 'nxt_P');

subtest({ # sat_P
    is_properLambdaFn($sat_P, 'sat_P');
    
    my $eq-a = $Str-eq('a');

    is_None $sat_P($eq-a)(''),                      '(sat_P (eq? "a") "")  ~>  None';
    is_None $sat_P($eq-a)('b'),                     '(sat_P (eq? "a") "b")  ~>  None';
    is_None $sat_P($eq-a)('ba'),                    '(sat_P (eq? "a") "ba")  ~>  None';
    is_Some $sat_P($eq-a)('a'),  $Pair('a', ''),    '(sat_P (eq? "a") "a")';
    is_Some $sat_P($eq-a)('ab'), $Pair('a', 'b'),   '(sat_P (eq? "a") "ab")';
}, 'sat_P');


subtest({ # seq_P aka bind_Parser
    is_properLambdaFn($seq_P, 'seq_P');
    
    my $s = 'some string';

    is_None($seq_P($fail_P, $return_P)($s),                                 "(fail_P >>= return_P) {$s.perl}  ~> None");
    is_Some($seq_P($return_P(42), $return_P)($s),           $Pair(42, $s),  "((return_P 42) >>= return_P) {$s.perl}");
    is_None($seq_P($return_P(23), -> Mu { $fail_P })($s),                   "((return_P 23) >>= λ_.fail_P) {$s.perl}");
}, 'seq_P');


subtest({ # alt_P aka choice_Parser
    is_properLambdaFn($alt_P, 'alt_P');
    
    my $s = 'some string';
    
    is_None($alt_P($fail_P, $fail_P)($s),                               "(fail_P >>= fail_P) {$s.perl}  ~>  None");
    is_Some($alt_P($fail_P, $return_P(23))($s),         $Pair(23, $s),  "(fail_P >>= (return_P 23)) {$s.perl}");
    is_Some($alt_P($return_P(23), $fail_P)($s),         $Pair(23, $s),  "((return_P 23) >>= fail_P) {$s.perl}");
    is_Some($alt_P($return_P(23), $return_P(42))($s),   $Pair(23, $s),  "((return_P 23) >>= (return_P 42)) {$s.perl}");
}, 'alt_P');


subtest({ # chr_P
    is_properLambdaFn($chr_P, 'chr_P');
    
    my $as = 'aaaa';
    
    is_None($chr_P('b')(''),                       '(chr_P "b" "")  ~>  None');
    is_None($chr_P('b')($as),                      '(chr_P "b" {$as.perl})  ~>  None');
    is_Some($chr_P('a')($as), $Pair('a', 'aaa'),   '(chr_P "a" {$as.perl})');
    is_Some($chr_P('a')('a'), $Pair('a', ''),      '(chr_P "a" "a")');
}, 'char_P');



subtest({ # many_P
    is_properLambdaFn($many_P, 'many_P');
    
    my $many-as = $many_P($chr_P('a'));

    is_Some($many-as(''),   $Pair([],           ''),    '(many_P (chr_P "a") "")');
    is_Some($many-as('a'),  $Pair(['a'],        ''),    '(many_P (chr_P "a") "a")');
    is_Some($many-as('aa'), $Pair(['a', 'a'],   ''),    '(many_P (chr_P "a") "aa")');

    is_Some($many-as('b'),   $Pair([],          'b'),   '(many_P (chr_P "a") "b")');
    is_Some($many-as('ab'),  $Pair(['a'],       'b'),   '(many_P (chr_P "a") "ab")');
    is_Some($many-as('aab'), $Pair(['a', 'a'],  'b'),   '(many_P (chr_P "a") "aab")');


    my $many-any = $many_P($nxt_P);

    is_Some($many-any(''),      $Pair([],               ''),    '(many_P nxt_P "")');
    is_Some($many-any('a'),     $Pair(['a'],            ''),    '(many_P nxt_P "a")');
    is_Some($many-any('ab'),    $Pair(['a', 'b'],       ''),    '(many_P nxt_P "ab")');
    is_Some($many-any('abc'),   $Pair(['a', 'b', 'c'],  ''),    '(many_P nxt_P "abc")');
}, 'many_P');

subtest({ # many1_P
    is_properLambdaFn($many1_P, 'many1_P');
    
    my $many1-as = $many1_P($chr_P('a'));
    
    is_None($many1-as(''),                              '(many1_P (chr_P "a") "")  ~>  None');
    is_Some($many1-as('a'),  $Pair(['a'],        ''),   '(many1_P (chr_P "a") "a")');
    is_Some($many1-as('aa'), $Pair(['a', 'a'],   ''),   '(many1_P (chr_P "a") "aa")');

    is_None($many1-as('b'),                             '(many1_P (chr_P "a") "b")  ~>  None');
    is_Some($many1-as('ab'),  $Pair(['a'],        'b'), '(many1_P (chr_P "a") "ab")');
    is_Some($many1-as('aab'), $Pair(['a', 'a'],   'b'), '(many1_P (chr_P "a") "aab")');


    my $many1-any = $many1_P($nxt_P);

    is_None($many1-any(''),                                      '(many1_P nxt_P "")  ~>  None');
    is_Some($many1-any('a'),     $Pair(['a'],            ''),    '(many1_P nxt_P "a")');
    is_Some($many1-any('ab'),    $Pair(['a', 'b'],       ''),    '(many1_P nxt_P "ab")');
    is_Some($many1-any('abc'),   $Pair(['a', 'b', 'c'],  ''),    '(many1_P nxt_P "abc")');
}, 'many1_P');

