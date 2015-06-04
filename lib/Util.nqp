#!nqp

class Util {

    method min($a, $b) { $a < $b ?? $a !! $b }
    method max($a, $b) { $a > $b ?? $a !! $b }

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


sub min($a, $b) is export { Util.min($a, $b) }
sub max($a, $b) is export { Util.max($a, $b) }
sub whatsit($v) is export { Util.whatsit($v) }

sub istype($subject, *@types)                    is export { Util.istype($subject, |@types) }

sub linesFrom(str $filename, $from = 1, $count?) is export { Util.linesFrom($filename, $from, $count) }
