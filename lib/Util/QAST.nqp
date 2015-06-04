#!nqp
use QAST;   # that is, nqp's

use Util;


role StrByDump is export {
    method Str() { dump(self) }
}

# Don't export this - only a workaround for the weird problems with exporting subs
# (can call them from outside but then they in turn cannot call themselves)
class Util::QAST {
    
    method dump($node, $parent = nqp::null, :$indent = '', :$oneLine = 0) {
        my $clsStr := nqp::substr($node.HOW.name($node), 6);
        
        my $isBlockChild := istype($parent, QAST::Block);
        my $isOrphan     := nqp::isnull($parent);
        my $siblingCount := $isOrphan ?? 0 !! nqp::elems($parent.list) - 1;
        my $isLastChild  := $isOrphan || ($parent.list[$siblingCount] =:= $node);
        my $prefix := $indent;
        if $isOrphan {
            $prefix := $prefix ~ '─'
        } elsif $isBlockChild {
            $prefix := $prefix ~ ($isLastChild ?? '╙' !! '╟' );
        } else {
            $prefix := $prefix ~ ($isLastChild ?? '└' !! '├' );
        }

        unless istype($node, QAST::Node) && nqp::defor($node, 0) {
            #nqp::die("cannot dump " ~ whatsit($node));
            if $oneLine {
                return '(' ~ whatsit($node) ~ ')';
            } else {
                return $prefix ~ '► ' ~ whatsit($node);
            }
        }

        my $matchStr := '';
        if $node.node && !istype($node, QAST::Var, QAST::IVal, QAST::NVal, QAST::SVal) {
            $matchStr := nqp::escape(~$node.node);
            if nqp::chars($matchStr) > 54 {
                $matchStr := nqp::substr($matchStr, 0, 51) ~ '"...'
            } else {
                $matchStr := $matchStr ~ '"';
            }
            $matchStr := '  ««"' ~ $matchStr;
        }

        my $extraStr := $node.dump_extra_node_info;
        $extraStr := $extraStr ?? ' ' ~ $extraStr !! '';
        
        my $specialStr := '';
        if istype($node, QAST::SpecialArg) {
            $clsStr := nqp::substr($clsStr, 0, nqp::index($clsStr, '+{'));
            $specialStr := $specialStr ~ ' :flat(' ~ $node.flat ~ ')' if $node.flat;
            my $nm := $node.named;
            if $nm {
                if nqp::isstr($nm) {
                    $specialStr := $specialStr ~ ' :named("' ~ nqp::escape($nm) ~ '")';
                } else {
                    $specialStr := $specialStr ~ ' :named(' ~ $nm ~ ')';
                }
            }
        }

        my %annotations := nqp::getattr($node, QAST::Node, '%!annotations');
        if %annotations {
            $specialStr := $specialStr ~ ' :annotations(' ~ whatsit(%annotations) ~ ')';
        }


        if $clsStr eq 'Op' {
            $extraStr := nqp::substr($extraStr, 1);
            $clsStr := $extraStr;
            $extraStr := '';
            $prefix := $prefix ~ '─';
        } elsif istype($node, QAST::Var) {
            $clsStr := istype($node, QAST::VarWithFallback)
                ?? '┬' ~ $clsStr
                !! '';
            $prefix := $prefix ~ '○';
            if $node.slurpy {
                $specialStr := $specialStr ~ ' :slurpy(' ~ $node.slurpy ~ ')'
            }
            unless ($node.default =:= NO_VALUE) {
                $specialStr := $specialStr 
                    ~ ' :default' ~ dump($node.value, :oneLine(1));
                    #~ ' :default(' ~ whatsit($node.value) ~ ')';
            }
            if istype($node, QAST::VarWithFallback) && $node.fallback {
                $specialStr := $specialStr ~ ' :fallback' ~ dump($node.fallback, :oneLine(1));
            }
        } elsif nqp::substr($clsStr, 1, 3) eq 'Val' {
            $prefix := $prefix ~ '◙ ';
            if istype($node, QAST::SVal) {
                $extraStr := ' "' ~ nqp::escape($node.value) ~ '"';
            } elsif istype($node, QAST::IVal, QAST::NVal) {
                $extraStr := ' ' ~ ~$node.value;
            }
        } elsif istype($node, QAST::Block) {
            $prefix := $prefix ~ '─:';
            my $bt := $node.blocktype;
            if $bt && $bt ne 'declaration' { # don't show default
                $specialStr := $specialStr ~ ' :blocktype(' ~ $bt ~ ')';
            }
        } elsif istype($node, Stmts) {
            $prefix := $prefix ~ '─:';
        } else {
            $prefix := $prefix ~ '─';
        }
        
        my $suffix := $matchStr;
        my $sep    := "\n";
        my $before := '';
        my $after  := '';
        if $oneLine {
            $prefix := '(';
            $suffix := ')';
            $sep    := ' ';
            if nqp::elems($node.list) > 0 {
                $before := '(';
                $after  := ')';
            }
        }
        my @lines := [$prefix  ~ $clsStr ~ $extraStr ~ $specialStr ~ $suffix];
        #my @lines := [$prefix ~ $node.HOW.name($node) ~ ($extraStr ?? '(' ~ $extraStr ~ ')' !! '') ~ $matchStr];
        my $childIndent := $indent ~ ($isLastChild ?? '  ' !! ($isBlockChild ?? '║ ' !! '│ '));
        for $node.list {
            @lines.push(dump($_, $node, :indent($childIndent), :$oneLine));
        }
        $before ~ nqp::join($sep, @lines) ~ $after;
    }

}


sub dump($node, $parent = nqp::null, :$indent = '', :$oneLine = 0) is export {
    Util::QAST.dump($node, $parent, :$indent, :$oneLine);
}

