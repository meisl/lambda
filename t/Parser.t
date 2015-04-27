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

plan 10;


sub is_Some($maybe, $expectedValue, Str $msg?) {
    subtest {
        does_ok($maybe, TMaybe)
            and
        case-Maybe($maybe,
            None => { ok(False, $msg // "expected a Some but got None") },
            Some => -> $v {
                my $expected = $Some(convert2Lambda($expectedValue));
                is "(Some $v)", $expected, $msg;  # TODO: improve msg
            }
        );
    };
}

sub is_None($maybe, Str $msg?) {
    subtest {
        does_ok($maybe, TMaybe)
            and
        case-Maybe($maybe,
            None => { ok(True, $msg) },
            Some => -> $v { ok(False, $msg // "expected a None but got (Some " ~ $v ~ ")") }
        );
    };
}




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


subtest({ # str_P
    is_properLambdaFn($str_P, 'str_P');
    
    my $s = 'some string';
    
    is_None($str_P('foo')($s),                                      "(str_P 'foo' {$s.perl})  ~> None");
    is_Some($str_P('')($s),             $Pair('', 'some string'),   "(str_P '' {$s.perl})");
    is_Some($str_P('s')($s),            $Pair('s', 'ome string'),   "(str_P 's' {$s.perl})");
    is_Some($str_P('so')($s),           $Pair('so', 'me string'),   "(str_P 'so' {$s.perl})");
    is_Some($str_P('som')($s),          $Pair('som', 'e string'),   "(str_P 'som' {$s.perl})");
    is_Some($str_P('some')($s),         $Pair('some', ' string'),   "(str_P 'some' {$s.perl})");
    is_Some($str_P('some ')($s),        $Pair('some ', 'string'),   "(str_P 'some ' {$s.perl})");
    
    is_None($str_P('some stringXXX')($s),                           "(str_P 'some stringXXX' {$s.perl})  ~>  None");
}, 'string_P');




subtest({ # many_P
    is_properLambdaFn($many_P, 'many_P');
    
    my $many-as = $many_P($chr_P('a'));

    is_Some($many-as(''),   $Pair([],           ''),    '(many_P (chr_P "a") "")');
    is_Some($many-as('a'),  $Pair(['a'],        ''),    '(many_P (chr_P "a") "a")');
    is_Some($many-as('aa'), $Pair(['a', 'a'],   ''),    '(many_P (chr_P "a") "aa")');

    is_Some($many-as('b'),   $Pair([],          'b'),   '(many_P (chr_P "a") "b")');
    is_Some($many-as('ab'),  $Pair(['a'],       'b'),   '(many_P (chr_P "a") "ab")');
    is_Some($many-as('aab'), $Pair(['a', 'a'],  'b'),   '(many_P (chr_P "a") "aab")');
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
}, 'many1_P');

