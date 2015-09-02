use NQPHLL;

use Util;
use Util::QAST;


class Util::Compiler {

    method loc2str(%l) {
        my $varNameStr := nqp::existskey(%l, 'var')
            ?? '  (' ~ %l<var>.name ~ ')'
            !! ''
        ;
        '   at ' ~ %l<str> ~ $varNameStr;
    }

    method match2location($match) {
        my @lines := nqp::split("\n", nqp::substr($match.orig, 0, $match.from == 0 ?? $match.chars !! $match.from));
        my $lineN := nqp::elems(@lines);
        my $colN  := 1 + nqp::chars(@lines.pop);
        my $file := $*USER_FILE;
        hash(:file($file), :line($lineN), :column($colN), :match($match), :str("$file:$lineN:$colN"));
    }

    method panic($match, *@msg-pieces) {
        if nqp::isconcrete($match) {
            @msg-pieces.push("\n");
            @msg-pieces.push(self.loc2str(self.match2location($match)));
        }
        nqp::die(join('', @msg-pieces));
    }
}


sub loc2str(%l)                 is export { Util::Compiler.loc2str(%l) }
sub match2location($match)      is export { Util::Compiler.match2location($match) }
sub panic($match, *@msg-pieces) is export { Util::Compiler.panic($match, |@msg-pieces) }

