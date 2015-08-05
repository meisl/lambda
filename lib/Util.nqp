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
            nqp::die("istype expects only type arguments or null or null_s after subject - encountered " ~ self.describe($_))
                if nqp::isconcrete($_) && !nqp::isnull_s($_);
            # Note: nqp::isconcrete(nqp::null_s) is true, but nqp::isconcrete(nqp::null) is false

            if nqp::isnull($_) {
                $out := 1 if nqp::isnull($subject);     # Note: nqp::isnull(nqp::isnull_s) is false
            } elsif nqp::isnull_s($_) {
                $out := 1 if nqp::isnull_s($subject);
            } elsif $_ =:= str {
                $out := 1 if nqp::isstr($subject);
            } elsif $_ =:= int {
                $out := 1 if nqp::isint($subject);
            } elsif $_ =:= num {
                $out := 1 if nqp::isnum($subject);
            } else {
                $out := 1 if nqp::istype($subject, $_);
            }
        }
        $out;
    }

    method insist-isa($n, $type) {
        (!self.istype($n, $type) # istype will complain if $type ain't a Type object
            && nqp::die('expected a ' ~ nqp::how($type).name($type) ~ ' - got ' ~ describe($n)));
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
sub insist-isa($subject, $type)                  is export { Util.insist-isa($subject, $type) }

sub linesFrom(str $filename, $from = 1, $count?) is export { Util.linesFrom($filename, $from, $count) }




sub MAIN(*@ARGS) {
    say(nqp::isconcrete(nqp::null));
    say(nqp::isconcrete(nqp::null_s));
    say(nqp::isnull(nqp::null_s));
}

