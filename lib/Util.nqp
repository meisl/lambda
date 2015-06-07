#!nqp

class Util {

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
            $out := "$x (int)";
        } elsif nqp::isnum($x) {
            $out := "$x (num)";
        } elsif nqp::isstr($x) {
            if nqp::isnull_s($x) {
                $out := 'nqp::null_s (str)';
            } else {
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

    method whatsit($v) {
        my $reprname := nqp::reprname($v);

        if nqp::isstr($v) {
            my $length := nqp::chars($v);
            if $length > 80 {
                return '"' ~ nqp::escape(nqp::substr($v, 0, 45)) ~ '"'
                     ~ ' ~ ... ~ '
                     ~ '"' ~ nqp::escape(nqp::substr($v, $length - 25)) ~ '"'
               ;
            } else {
                return '"' ~ nqp::escape($v) ~ '"';
            }
        } elsif nqp::isint($v) || nqp::isnum($v) {
            return $reprname ~ ' ' ~ $v;
        } elsif nqp::ishash($v) {
            my @kvs := [];
            for $v {
                my $k := nqp::iterkey_s($_);
                my $v := nqp::iterval($_);
                @kvs.push(":$k(" ~ self.whatsit($v) ~ ')');
            }
            return 'hash(' ~ nqp::join(', ', @kvs) ~ ')';
        } elsif nqp::islist($v) {
            my @out := [];
            for $v {
                @out.push(self.whatsit($_));
            }
            return '[' ~ nqp::join(', ', @out) ~ ']';
        } elsif istype($v, QAST::Node) {
            my $s := $v.HOW.name($v);
            my $x := $v.dump_extra_node_info;
            return $x ?? "$s($x)" !! $s;
        #} elsif istype($v, Something) { ??? }
        } elsif nqp::isnull($v) {
            return $reprname;
        } else {
            my $how := nqp::how($v);
            if $how {
                return $how.name($v);
            } else {
                return $reprname;
            }
        }
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
            nqp::die("istype expects only type arguments after subject - encountered " ~ self.whatsit($_))
                if nqp::isconcrete($_);
            $out := 1 if nqp::istype($subject, $_);
        }
        return $out;
    }
}


sub min($a, $b)         is export { Util.min($a, $b)    }
sub max($a, $b)         is export { Util.max($a, $b)    }
sub unixify(str $path)  is export { Util.unixify($path) }
sub whatsit($v)         is export { Util.describe($v)   }
sub describe($x)        is export { Util.describe($x)   }

sub istype($subject, *@types)                    is export { Util.istype($subject, |@types) }

sub linesFrom(str $filename, $from = 1, $count?) is export { Util.linesFrom($filename, $from, $count) }
