#!nqp

class Util {
    method hash(*%adverbs) { %adverbs }

    method min($a, $b) { $a < $b ?? $a !! $b }
    method max($a, $b) { $a > $b ?? $a !! $b }

    method unixify(str $path) {
        nqp::join('/', nqp::split('\\', $path));
    }

    method describe_fallback($x) {
        my $out;
        my $how := nqp::how($x);
        if $how {
            $out := $how.name($x);
        } else {
            $out := nqp::reprname($x);
        }
        
        unless nqp::isconcrete($x) {
            $out := $out ~ ', Type object'
        }
        if nqp::isinvokable($x) {
            $out := $out ~ ', invokable';
        }
        $out;
    }

    method describe($x) {
        my $out;
        if nqp::isint($x) {
            $out := nqp::isconcrete($x) ?? "$x (int)" !! '(' ~ self.describe_fallback($x) ~ ')';
        } elsif nqp::isnum($x) {
            $out := nqp::isconcrete($x) ?? "$x (num)" !! '(' ~ self.describe_fallback($x) ~ ')';
        } elsif nqp::isstr($x) {
            if nqp::isnull_s($x) {
                $out := 'nqp::null_s (str)';
            } elsif nqp::isconcrete($x) {
                my $length := nqp::chars($x);
                if $length > 80 {
                    $out := '"' ~ nqp::escape(nqp::substr($x, 0, 45)) ~ '"'
                         ~ ' ~ ... ~ '
                         ~ '"' ~ nqp::escape(nqp::substr($x, $length - 25)) ~ '"'
                         ~ ' (str)'
                   ;
                } else {
                    $out := '"' ~ nqp::escape($x) ~ '" (str)';
                }
            } else {
                $out := '(' ~ self.describe_fallback($x) ~ ')';
            }
        } elsif nqp::isnull($x) {   # note: nqp::null_s would NOT pass the nqp::isnull test
            $out := 'nqp::null';
        } elsif nqp::ishash($x) {
            my @pairs := [];
            for $x {
                @pairs.push('"' ~ nqp::escape(nqp::iterkey_s($_)) ~ '"');
                @pairs.push(self.describe(nqp::iterval($_)));
            }
            $out := '#`{' ~ self.describe_fallback($x) ~ ':}nqp::hash( ' ~ nqp::join(', ', @pairs) ~ ' )';
        } elsif nqp::islist($x) {
            my @out := [];
            for $x {
                @out.push(self.describe($_));
            }
            $out := '#`{' ~ self.describe_fallback($x) ~ ':}[ ' ~ nqp::join(', ', @out) ~ ' ]';
        } elsif nqp::istype($x, QAST::Node) && nqp::isconcrete($x) {
            $out := $x.HOW.name($x);
            my $extra := $x.dump_extra_node_info;
            $out := "$out($extra)" if $extra;
        } else {
            $out := self.describe_fallback($x);
            if 0 && nqp::can($x, 'Str') {
                $out := '#`{(' ~ $out ~ ').Str:}"';
                $out := $out ~ nqp::escape($x.Str) ~ '"';
            } else {
                $out := "($out)";
            }
        }
        $out;
    }

    method trim(str $s) {
        my int $n := nqp::chars($s);
        my int $i := 0;
        while nqp::eqat($s, ' ', $i) && ($i < $n) {
            $i++;
        }
        if $i == $n {
            '';
        } else {
            $n--;
            while nqp::eqat($s, ' ', $n) {
                $n--;
            }
            nqp::substr($s, $i, $n - $i + 1);
        }
    }

    method join(str $sep, @pieces, :$prefix1st = 0, :$filter, :$map) {
        my $n := nqp::elems(@pieces);
        return ''
            unless $n;

        $filter  := -> $x { 1 }  unless $filter;
        $map     := -> $x { $x } unless $map;
        my $map1 := -> $x { my $y := $map($x); nqp::isstr($y) ?? $y !! self.describe($y) };
        my @strs := [];
        for @pieces {
            @strs.push($map1($_)) 
                if $filter($_);
        }
        my $out := nqp::join($sep, @strs);
        $prefix1st ?? $sep ~ $out !! $out;
    }

    method say(*@pieces) {
        nqp::say(self.join(
            '', 
            @pieces, 
            :map(-> $x { # make it behave like normal nqp::say
                if nqp::isnull($x) || nqp::isnull_s($x) { # must test this 1st because nqp::isstr(nqp::null_s) is true
                    ''
                } elsif nqp::isstr($x) || nqp::isint($x) || nqp::isnum($x) {
                    ~$x
                } else {
                    $x
                }
            })
        ));
    }

    method linesFrom(str $filename, $from = 1, $count?) {
        my $to := $from - 1 + nqp::defor($count, nqp::inf());
        my @out := [];
        my $fh := nqp::open($filename, 'r');
        nqp::setinputlinesep($fh, "\n");
        my $linesRead := 0;
        while !nqp::eoffh($fh) && ($linesRead < $to) {
            my $line := nqp::readlinefh($fh);
            $linesRead++;
            @out.push($line) unless $linesRead < $from;
        }
        nqp::closefh($fh);
        @out;
    }

    method istype($subject, *@types) {
        nqp::die("istype expects at least one type argument after subject - got none")
            unless @types;
        my $out := 0;
        for @types {
            nqp::die("istype expects only type arguments after subject - encountered " ~ self.describe($_))
                if nqp::isconcrete($_);
            $out := 1 if nqp::istype($subject, $_);
        }
        return $out;
    }
}


sub min($a, $b)         is export { Util.min($a, $b)    }
sub max($a, $b)         is export { Util.max($a, $b)    }
sub unixify(str $path)  is export { Util.unixify($path) }
sub describe($x)        is export { Util.describe($x)   }
sub say(*@pieces)       is export { Util.say(|@pieces)  }
sub trim(str $s)        is export { Util.trim($s)       }

sub join(str $sep, @pieces, :$prefix1st = 0, :$filter, :$map) is export { Util.join($sep, @pieces, :$prefix1st, :$filter, :$map) }

sub istype($subject, *@types)                    is export { Util.istype($subject, |@types) }

sub linesFrom(str $filename, $from = 1, $count?) is export { Util.linesFrom($filename, $from, $count) }




sub MAIN(*@ARGS) {
    my sub FALSE($n) { 0 }
    my sub TRUE($n) { 1 }
    
    my sub mkAnd(&f, &g) {
        if &f =:= &TRUE {
            &g;
        } elsif &f =:= &FALSE {
            &FALSE;
        } elsif &g =:= &TRUE {
            &f;
        } elsif &g =:= &FALSE {
            &FALSE;
        } else {
            -> $n { &f($n) && &g($n) }
        }
    }
    
    my sub mkOr(&f, &g) {
        if &f =:= &TRUE {
            &TRUE;
        } elsif &f =:= &FALSE {
            &g;
        } elsif &g =:= &TRUE {
            &TRUE;
        } elsif &g =:= &FALSE {
            &f;
        } else {
            -> $n { &f($n) || &g($n) }
        }
    }
    
    my sub mkCmp($v) {
        if nqp::isstr($v) {
            -> $u { nqp::isstr($u) && ($u eq $v) };
        } elsif nqp::isint($v) {
            -> $u { nqp::isint($u) && ($u == $v) };
        } elsif nqp::isnum($v) {
            -> $u { nqp::isnum($u) && ($u == $v) };
        } elsif nqp::isinvokable($v) {
            if nqp::how($v).name($v) eq 'NQPRegex' {
                -> $u { nqp::isstr($u) && ?($u ~~ $v) };
            } else {
                $v;
            }
        } else {
            -> $u { $u =:= $v };
        }
    }

    my sub mkCan(str $methodName) {
        -> $n { nqp::can($n, $methodName) }
    }
    

    my sub mkMethCmp(str $methodName, &cmp) {
        if &cmp =:= &FALSE {
            &FALSE;
        } elsif &cmp =:= &TRUE {
            -> $n { nqp::can($n, $methodName) };
        } else {
            -> $n { nqp::can($n, $methodName) && &cmp(nqp::callmethod($n, $methodName)) };
        }
    }

    my sub mkIdx(int $i) {
        nqp::die('mkIdx expects a non-negative int - got ' ~ describe($i))
            unless nqp::isint($i) && ($i >= 0);
        -> $n { $n[$i] }
    }

    my sub compose(&f, &g) {
        -> $n { &f(&g($n)) }
    }
    
    my sub template($type, *@children, *%attributes) {
        my $out := describe($type);
        my &test := -> $n { istype($n, $type) }
        for %attributes {
            my $k := nqp::iterkey_s($_);
            my $v := nqp::iterval($_);
            $out := $out ~ ', :' ~ $k ~ '(' ~ describe($v) ~ ')';
            my &attrTest := &FALSE;
            if nqp::islist($v) {
                for $v {
                    &attrTest := mkOr(mkCmp($_), &attrTest);
                }
            } else {
                &attrTest := mkCmp($v);
            }
            &test := mkAnd(&test, mkMethCmp($k, &attrTest));
        }

        my $i := 0;
        for @children {
            &test := mkAnd(&test, compose($_, mkIdx($i)));
            $i++;
        }
        say($out);
        &test;
    }
    
    my sub Π($type, *@children, *%attributes) {
        template($type, |@children, |%attributes)
    }
    
    
    my $pattern := Π(QAST::Op, :op<bind>,
        Π(QAST::Var, :name(/^'&'.+/), :decl<var static>),
        Π(QAST::Block),
        Π(QAST::Block)
    );
    say($pattern(
        QAST::Op.new(:op<bind>,
            QAST::Var.new(:name<&foo>, :decl<var>),
            QAST::Block.new(
                QAST::Var.new(:name<$x>, :decl<param>),
                QAST::Op.new(:op<call>, :name<&say>,
                    QAST::Var.new(:name<$x>)
                )
            )
        )
    ));

    $pattern := Π(QAST::Node, :name<&foo>, :decl<var param static>);
    say($pattern(QAST::Var.new(:name<&foo>, :decl<param>)));

    $pattern := Π(QAST::Var, :name(/^'&'.+/), :decl<var static>);
    say($pattern(QAST::Var.new(:name<&foo>, :decl<var>)));

    $pattern := Π(QAST::Var, :name(-> $n { nqp::index($n, '&') == 0 }), :decl<var static>);
    say($pattern(QAST::Var.new(:name<&foo>, :decl<var>)));

    
}




