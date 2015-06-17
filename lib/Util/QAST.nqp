#!nqp
use QAST;   # that is, nqp's

use Util;
use Util::TreeWalk;


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
            #nqp::die("cannot dump " ~ describe($node));
            if $oneLine {
                return '(' ~ describe($node) ~ ')';
            } else {
                return $prefix ~ '► ' ~ describe($node);
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

        my $extraStr := trim($node.dump_extra_node_info);
        
        my @specials := [];
        if istype($node, QAST::SpecialArg) {
            $clsStr := nqp::substr($clsStr, 0, nqp::index($clsStr, '+{'));
            @specials.push(':flat(' ~ $node.flat ~ ')') if $node.flat;
            my $nm := $node.named;
            if $nm {
                if nqp::isstr($nm) {
                    @specials.push(':named("' ~ nqp::escape($nm) ~ '")');
                } else {
                    @specials.push(':named(' ~ $nm ~ ')');
                }
            }
        }

        my %annotations := nqp::getattr($node, QAST::Node, '%!annotations');
        if %annotations {
            @specials.push(':annotations(' ~ describe(%annotations) ~ ')');
        }


        if $clsStr eq 'Op' {
            $clsStr := $extraStr;
            $extraStr := '';
            $prefix := $prefix ~ '─';
        } elsif istype($node, QAST::Var) {
            if istype($node, QAST::VarWithFallback) {
                $prefix := $prefix ~ '○';
                $clsStr := '┬' ~ $clsStr unless $oneLine;
            } else {
                $prefix := $prefix ~ '○ ';
                $clsStr := '';
            }
            if $node.slurpy {
                @specials.push(':slurpy(' ~ $node.slurpy ~ ')');
            }
            unless ($node.default =:= NO_VALUE) {
                @specials.push(':default' ~ self.dump($node.value, :oneLine));
            }
            if nqp::eqat($extraStr, 'lexical ', 0) {
                $extraStr := nqp::substr($extraStr, 8);
            }
            if istype($node, QAST::VarWithFallback) && $node.fallback {
                @specials.push(':fallback' ~ self.dump($node.fallback, :oneLine));
            }
        } elsif nqp::substr($clsStr, 1, 3) eq 'Val' {
            $prefix := $prefix ~ '◙ ';
            if istype($node, QAST::SVal) {
                $extraStr := '"' ~ nqp::escape($node.value) ~ '"';
            } elsif istype($node, QAST::IVal, QAST::NVal) {
                $extraStr := ~$node.value;
            }
        } elsif istype($node, QAST::Block) {
            $prefix := $prefix ~ '─:';
            my $bt := $node.blocktype;
            if $bt && $bt ne 'declaration' { # don't show default
                @specials.push(':blocktype(' ~ $bt ~ ')');
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
        $extraStr := ' ' ~ $extraStr
            if $extraStr ne '';
        my @lines := [$prefix ~ trim($clsStr ~ $extraStr ~ join(' ', @specials, :prefix1st)) ~ $suffix];
        #my @lines := [$prefix ~ $node.HOW.name($node) ~ ($extraStr ?? '(' ~ $extraStr ~ ')' !! '') ~ $matchStr];
        my $childIndent := $indent ~ ($isLastChild ?? '  ' !! ($isBlockChild ?? '║ ' !! '│ '));
        for $node.list {
            @lines.push(self.dump($_, $node, :indent($childIndent), :$oneLine));
        }
        $before ~ nqp::join($sep, @lines) ~ $after;
    }

    method qastChildren($ast, *@types) {
        nqp::die('qastChildren expects a QAST::Node as 1st arg - got ' ~ nqp::reprname($ast) )
            unless istype($ast, QAST::Node);
        my @out := [];
        if nqp::elems(@types) == 0 {
            @types := [QAST::Node];
        }
        for $ast.list {
            if istype($_, |@types) {
                @out.push($_);
            }
        }
        @out;
    }

    method removeChild($parent, $child) {
        my @children := nqp::islist($parent) ?? $parent !! $parent.list;
        my @foundAt := [];
        my $i := 0;
        my $n := nqp::elems(@children);
        for @children {
            if $_ =:= $child {
                @foundAt.push($i);
            }
            $i++;
        }
        unless +@foundAt {
            nqp::die("could not find child " ~ describe($child) ~ ' under ' ~ self.dump($parent));
        }

        my @removed := [];
        @foundAt.push($n);
        $i := @foundAt.shift;
        my $k := $i + 1;
        for @foundAt {
            while $k < $_ {
                @children[$i++] := @children[$k++];
            }
            @removed.push(@children[$k++]);
        }
        nqp::setelems(@children, $n - nqp::elems(@removed));
        $parent;
    }

    method findPath(&test, $node, @pathUp = []) {
        my $res := &test($node, @pathUp);
        if nqp::islist($res) {
            @pathUp.unshift($node);
            for $res {
                my $res2 := self.findPath(&test, $_, @pathUp);
                return $res2 if $res2;  # ie. if truthy (list, 1 or a node)
            }
            @pathUp.shift();
        } elsif $res {
            if $res =:= $node || !istype($res, QAST::Node) {    # just truthy to indicate that $node should be returned
                return $node
            } else {
                while !($res =:= @pathUp.shift) {   # eat path up till we find the node
                }
                return $res;
            }
        }
        return nqp::null;
    }

    method findPaths(&test, $ast) {
        my @out := [];
        TreeWalk.dfs-up(
            -> $n, @p { # probe
                TreeWalkDo.recurse(:take(&test($n, @p)));
            },
            -> $n, @p { # consume
                my @path := nqp::clone(@p);
                @path.unshift($n);
                @out.push(@path);
            },
            $ast
        );
        @out;
    }

    method fix_var_attrs($ast) {
        TreeWalk.dfs-up(
            -> $n, @p { TreeWalkDo.recurse(:take(istype($n, QAST::Var))) },
            -> $n, @p {
                $n.decl(nqp::null_s)
                    unless $n.decl;
                $n.scope('lexical')     # (at least) QASTCompilerMAST expects var (decl)s to have explicit scope
                    unless $n.scope;
            },
            $ast
        );
    }

    my sub _drop_Stmts($ast, $parent) {
        nqp::die('dropStmts expects a QAST::Node - got ' ~ nqp::reprname($ast) ~ (nqp::isstr($ast) ?? ' "' ~ nqp::escape($ast) ~ '"' !! '') )
            unless istype($ast, QAST::Node);

        if nqp::can($ast, 'resultchild') && nqp::isint($ast.resultchild) && nqp::elems($ast.list) != $ast.resultchild + 1 {
            return [$ast];   # don't muck with that...
        }

        my @children := [];
        for $ast.list {
            for _drop_Stmts($_, $ast) {
                @children.push($_);
            }
        }
        if istype($ast, QAST::Stmts)    # do not remove Stmt!
            && !nqp::isnull($parent)
            && (
                  istype($parent, QAST::CompUnit, QAST::Block, QAST::Stmts, QAST::Stmt) 
               || (nqp::elems(@children) < 2)
            )
        {
            return @children; # return the Stmts' children as is, dropping the Stmts node
        } else {
            #$ast.set_children(@children);
            my @list := $ast.list;
            while +@list { @list.pop }
            for @children { @list.push($_) }
            if istype($ast, QAST::Stmts, QAST::Stmt) && nqp::isint($ast.resultchild) {  # fixup :resultchild if necessary
                #$ast.resultchild(nqp::elems(@children) - 1);
                nqp::bindattr($ast, QAST::Stmts, '$!resultchild', NO_VALUE);
            }
        }

        return [$ast];
    }

    method drop_Stmts($ast) {
        _drop_Stmts($ast, nqp::null)[0];
    }

}


sub dump($node, $parent = nqp::null, :$indent = '', :$oneLine = 0) is export {
    Util::QAST.dump($node, $parent, :$indent, :$oneLine);
}

sub qastChildren($ast, *@types)     is export { Util::QAST.qastChildren($ast, |@types) }
sub removeChild($parent, $child)    is export { Util::QAST.removeChild($parent, $child) }
sub findPath(&test, $node, @pathUp = []) is export { Util::QAST.findPath(&test, $node, @pathUp) }

sub findPaths(&test, $ast)          is export { Util::QAST.findPaths(&test, $ast) }
sub fix_var_attrs($ast)             is export { Util::QAST.fix_var_attrs($ast) }
sub drop_Stmts($ast)                is export { Util::QAST.drop_Stmts($ast) }
