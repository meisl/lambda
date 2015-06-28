#!nqp

use Util;

class Backtrace is export {

    class Frame is export {
        has %!fields is associative_delegate;

        method BUILD(:$raw_frame!, :$raw_framestring!) {
            %!fields := hash(
                :$raw_frame,
                :$raw_framestring,
                :sub($raw_frame<sub>),
                :file_src($raw_frame<annotations><file>),
                :line_src($raw_frame<annotations><line>),
            );
            self.init(|%!fields);
        }

        method init(:$raw_frame!, :$raw_framestring!, :$sub!, :$file_src!, :$line_src!) {
            
            # XXX: rather hacky from here on...
            my $s := nqp::substr($raw_framestring, 6); # ignore "   at "/" from " prefix
            my @parts := nqp::split(':' ~ $line_src ~ '  (', $s);
            my $file_src_alt := @parts[0];
            my str $bin_part := nqp::split(')', @parts[1])[0];
            
            @parts := nqp::split(':', $bin_part);
            # work backwards now (via pop) in order to not get confused by ':' in file name (on Windows)
            unless +@parts {
                nqp::die('>>>> ' ~ describe($bin_part) ~ '|' ~ describe($raw_framestring) ~ '|' ~ @parts[1]);
            }
            %!fields<line_bin> := @parts.pop;
            %!fields<sub_name> := @parts.pop;
            %!fields<file_bin> := unixify(nqp::join(':', @parts));
            %!fields<file_src> := unixify($file_src_alt);
            
            # make some synonyms:
            %!fields<file> := %!fields<file_src>;
            %!fields<line> := %!fields<line_src>;
            self;
        }

        method Str(:$strip_cwd = 1) {
            my $fs := self<file_src>;
            my $fb := self<file_bin>;
            if $strip_cwd {
                my $cwd := unixify(nqp::cwd);
                my $n := nqp::chars($cwd) + 1; # one more for path separator
                my $i;
                $i := nqp::index($fs, $cwd);
                $fs := nqp::substr($fs, $n) unless $i;
                
                $i := nqp::index($fb, $cwd);
                $fb := nqp::substr($fb, $n) unless $i;
            }
            join('', :map(-> $x { ~$x }), [
                $fs,
                ':',
                self<line_src>,
                '  (',
                $fb,
                ':',
                self<sub_name>,
                ':',
                self<line_bin>,
                ')'
            ])
        }
        
    }

    has @!frames is positional_delegate;

    method new($error = NO_VALUE, int :$skip = 0) {
        if $error =:= NO_VALUE {
            try { nqp::die('WE ARE HERE'); CATCH { $error := $! } }
            $skip := $skip + 1; # if made here, then ignore the try block above
        }
        my $backtrace := nqp::iterator(nqp::backtrace($error));
        my @backtracestrings := nqp::backtracestrings($error);
        my @frames := [];
        for @backtracestrings -> $raw_framestring {
            my $raw_frame := nqp::shift($backtrace);
            @frames.push(Backtrace::Frame.new(:$raw_frame, :$raw_framestring))
                unless $skip > 0;
            $skip--;
        }
        self.bless(:@frames);
    }

    method BUILD(:@frames) {
        @!frames := @frames;
        self;
    }

    my $sysPrefix     := unixify(nqp::backendconfig()<prefix> ~ '/languages/nqp');
    my $sysPrefix_len := nqp::chars($sysPrefix);

    method filter($filter = NO_VALUE) {
        $filter := -> $x { 1 } if $filter =:= NO_VALUE;
        my @frames := [];
        for @!frames {
            if $filter($_) && nqp::substr($_<file_bin>, 0, $sysPrefix_len) ne $sysPrefix {
                @frames.push($_);
            }
        }
        my $out := nqp::clone(self).BUILD(:@frames);
        $out;
    }

    method list() { @!frames }

    method Str(:$strip_cwd = 1, :$prefix = '', :$prefix1st = 0) {
        $prefix1st := $prefix1st ?? $prefix !! '';
        my @frames := self.list;
        "$prefix1st   at " ~ 
            (+@frames
                ?? join("\n$prefix from ", @frames, :map(-> $frame { $frame.Str(:$strip_cwd) }))
                !! '<empty backtrace>')
    }

}
