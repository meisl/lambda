#!nqp

class Util {
    method hash(*%adverbs) { %adverbs }

    method min($a, $b) { $a < $b ?? $a !! $b }
    method max($a, $b) { $a > $b ?? $a !! $b }

    method unixify(str $path) {
        nqp::join('/', nqp::split('\\', $path));
    }

    method howName($x) {
        my $how := nqp::how($x);
        $how ?? $how.name($x)
             !! nqp::reprname($x);
    }

    method describe_fallback($x) {
        my $out := self.howName($x);
        
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
            if nqp::isnull_s($x) {  # Note: nqp::isconcrete(nqp::null_s()) is true
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
            $out := howName($x);
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
        my int $i := nqp::findnotcclass(nqp::const::CCLASS_WHITESPACE, $s, 0, $n);
        if $i == $n {
            '';
        } else {
            $n--;
            while nqp::findcclass(nqp::const::CCLASS_WHITESPACE, $s, $n, 1) == $n {
                $n--;
            }
            nqp::substr($s, $i, $n - $i + 1);
        }
    }

    method join(str $sep, $pieces, :$prefix1st = 0, :$filter, :$map) {
        nqp::die("expected a hash or a list - got " ~ describe($pieces))
            unless nqp::ishash($pieces) || nqp::islist($pieces);
        my $n := nqp::elems($pieces);
        if $n > 0 {
            if nqp::islist($pieces) {
                $map := -> $x { $x } unless $map;
            } else { # it's a hash
                $map := -> $x { '"' ~ nqp::escape($x.key) ~ '" => ' ~ self.describe($x.value) } unless $map;
            }
            $filter  := -> $x { 1 }  unless $filter;
            my $map1 := -> $x { my $y := $map($x); nqp::isstr($y) ?? $y !! self.describe($y) };
            my @strs := [];
            for $pieces {
                @strs.push($map1($_)) 
                    if $filter($_);
            }
            my $out := nqp::join($sep, @strs);
            $prefix1st ?? $sep ~ $out !! $out;
        } else {
            '';
        }
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
            if nqp::isconcrete($_) {
                # Note: nqp::isconcrete(nqp::null_s) is true, but nqp::isconcrete(nqp::null) is false
                if nqp::isnull_s($_) {
                    $out := 1 if nqp::isnull_s($subject);
                } else {
                    nqp::die("istype expects only type arguments or null or null_s after subject - encountered " ~ self.describe($_));
                }
            } elsif $_ =:= str {
                $out := 1 if nqp::isstr($subject);
            } elsif $_ =:= int {
                $out := 1 if nqp::isint($subject);
            } elsif $_ =:= num {
                $out := 1 if nqp::isnum($subject);
            } elsif nqp::isnull($_) {
                $out := 1 if nqp::isnull($subject);     # Note: nqp::isnull(nqp::isnull_s) is false
            } else {
                $out := 1 if nqp::istype($subject, $_);
            }
        }
        $out;
    }

    method map(@xs, &f) {
        my @out := [];
        for @xs {
            @out.push(&f($_));
        }
        @out;
    }

    method insist-isa($n, *@types, str :$desc) {
        unless self.istype($n, |@types) { # istype will complain if any of @types is a non-Type object
            my $msg := $desc ne '' ?? $desc ~ ': ' !! '';
            $msg := $msg ~ 'expected a '
                ~ self.join(' or a ', self.map(@types, -> $t { howName($t) } ))
                ~ ' - got ' ~ describe($n);
            nqp::die($msg);
        }
        0;
    }

    method flatten($args, :$map) {
        $map := -> $x { $x } unless $map;

        return [$map($args)]
            unless nqp::islist($args);

        my @out := [];
        for $args -> $arg {
            if nqp::islist($arg) {
                @out.push($map($_)) for $arg;
            } else {
                @out.push($map($arg));
            }
        }
        @out;
    }

    method super($self, str $method-name, @args, %adverbs) {
        my $method := nqp::findmethod($self.HOW.mro($self)[1], $method-name);
        $method($self, |@args, |%adverbs);
    }

}


sub min($a, $b)         is export { Util.min($a, $b)    }
sub max($a, $b)         is export { Util.max($a, $b)    }
sub unixify(str $path)  is export { Util.unixify($path) }
sub howName($x)         is export { Util.howName($x)    }
sub describe($x)        is export { Util.describe($x)   }
sub say(*@pieces)       is export { Util.say(|@pieces)  }
sub trim(str $s)        is export { Util.trim($s)       }

sub join(str $sep, @pieces, :$prefix1st = 0, :$filter, :$map) is export { Util.join($sep, @pieces, :$prefix1st, :$filter, :$map) }

sub istype($subject, *@types)                           is export { Util.istype($subject, |@types) }
sub insist-isa($subject, $type, *@types, str :$desc)    is export { Util.insist-isa($subject, $type, |@types, :$desc) }

sub linesFrom(str $filename, $from = 1, $count?) is export { Util.linesFrom($filename, $from, $count) }

sub flatten($args, :$map)                        is export { Util.flatten($args, :$map) }

sub super($self, str $method-name, *@args, *%adverbs) is export { Util.super($self, $method-name, @args, %adverbs) }


sub MAIN(*@ARGS) {
}

