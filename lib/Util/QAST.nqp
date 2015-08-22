#!nqp

use Util;
use Util::TreeWalk;

my class NO_VALUE {}


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
            unless ($node.default =:= NQPMu) {
                @specials.push(':default' ~ self.dump($node.default, :oneLine));
            }
            if nqp::eqat($extraStr, 'lexical ', 0) { # don't show default :decl
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
            if $bt && $bt ne 'declaration' { # don't show default :blocktype
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
                $n.name(nqp::null_s)
                    unless $n.name;
                $n.decl(nqp::null_s)
                    unless $n.decl;
                $n.scope('lexical')     # (at least) QASTCompilerMAST expects var (decl)s to have explicit scope
                    unless $n.scope;
            },
            :children(-> $n {
                if istype($n, QAST::Node) {
                    my @out := $n.list;
                    if istype($n, QAST::Var) && istype($n.default, QAST::Node) || istype($n, QAST::VarWithFallback) && istype($n.fallback, QAST::Node) {
                        @out := nqp::clone(@out);
                        @out.push($n.default)
                            if istype($n.default, QAST::Node);
                        @out.push($n.fallback)
                            if istype($n, QAST::VarWithFallback) && istype($n.fallback, QAST::Node);
                    }
                    @out;
                } else {
                    [];
                }
            }),
            $ast
        );
    }

    method drop_Stmts($ast) {
        TreeWalk.dfs-up(
            -> $n, @p {
                my $take := istype($n, QAST::Stmts);    # do not remove Stmt (singular, no trailing "s")!
                if $take && nqp::isint($n.resultchild) {
                    $take := $n.resultchild == nqp::elems($n.list) - 1;
                }
                TreeWalkDo.recurse(:$take);
            },
            -> $n, @p {
                if @p {
                    my $parent := @p[0];
                    if istype($parent, QAST::Stmts, QAST::Stmt) {
                        my $i := 0;
                        $i++ until $n =:= $parent[$i];  # TODO: index alredy available in dfs-up...
                        my $r := $parent.resultchild;
                        my $s := nqp::elems($parent);
                        # TODO: don't remove empty Stmts if in result position
                        if nqp::isint($r) {
                            my $l := nqp::elems($n);
                            if $i <= $r {
                                $r := $r + $l - 1;
                            }
                            if $r == $s + $l - 2 {  # new nr of parent's children
                                nqp::bindattr(
                                    $parent, 
                                    istype($parent, QAST::Stmts) ?? QAST::Stmts !! QAST::Stmt, 
                                    '$!resultchild',
                                    nqp::null
                                );
                            } else {
                                $parent.resultchild($r);
                            }
                        }
                        TreeWalk.replace(|$n.list);
                    } elsif istype($parent, QAST::CompUnit, QAST::Block) || nqp::elems($n) < 2 {
                        # TODO: don't remove empty Stmts if in result position
                        TreeWalk.replace(|$n.list);
                    }
                } else { # is topmost node
                    if nqp::elems($n) == 1 {
                        TreeWalk.replace($n[0]);
                    }
                }
            },
            $ast
        )
    }

    method drop_takeclosure($ast) {
        TreeWalk.dfs-up(
            -> $n, @p { TreeWalkDo.recurse(:take(istype($n, QAST::Op) && $n.op eq 'takeclosure')) },
            -> $n, @p {
                my $child := $n[0];
                unless (nqp::elems($n.list) == 1) && istype($child, QAST::Block) {
                    nqp::die('cannot handle ' ~ dump($n));
                }
                if istype($n, QAST::SpecialArg) {
                    $child.flat($n.flat);
                    $child.named($n.named);
                }
                TreeWalk.replace($child);
            },
            $ast
        )
    }

    method replace_assoc_and_pos_scoped($ast) {
        TreeWalk.dfs-up(
            -> $n, @p {
                my $take := istype($n, QAST::VarWithFallback);
                if $take {
                    if @p {    # ~> always visit if it's the top node - otherwise check parent:
                        my $opn := istype(@p[0], QAST::Op) ?? @p[0].op !! nqp::null;
                        if $opn {
                            $take := ($opn ne 'postinc') && ($opn ne 'postdec') && ($opn ne 'preinc') && ($opn ne 'predec');
                        }
                   }
                }
                TreeWalkDo.recurse(:$take);
            },
            -> $n, @p {
                my $scope := $n.scope;
                my $op;
                if $scope eq 'positional' {
                    $op := 'pos';
                } elsif $scope eq 'associative' {
                    $op := 'key';
                }
                my $out;
                if $op {
                    my $parent := @p[0];
                    if istype($parent, QAST::Op) && ($parent.op eq 'bind') && ($n =:= $parent[0]) {
                        $parent.op('bind' ~ $op);   # bindpos or bindkey
                        $out := TreeWalk.replace(|$n.list);  # replace ourselves ($n, VarWithFallback) with our children
                    } else {
                        $out := QAST::Op.new(:op('at' ~ $op),
                            :node($n.node),
                            |$n.list
                        );
                        my $fallback := $n.fallback;
                        unless nqp::isnull($fallback) {
                            #$out := QAST::Op.new(:op<if>,
                            #    QAST::Op.new(:op('exists' ~ $op), 
                            #        nqp::clone($n[0]),
                            #        nqp::clone($n[1]),
                            #    ),
                            #    $out,
                            #    $fallback
                            #);
                            $out := QAST::Op.new(:op<ifnull>,
                                $out,
                                $fallback
                            );
                        }
                        if istype($n, QAST::SpecialArg) {
                            $out.named($n.named);
                            $out.flat($n.flat);
                        }
                        $out := TreeWalk.replace($out);
                    }
                }
                $out;
            },
            $ast
        );
    }


    method remove_bogusOpNames($ast) {
        TreeWalk.dfs-up(
            -> $n, @p {
                my $take := istype($n, QAST::Op)
                    && ($n.op ne 'call')
                    && ($n.op ne 'callstatic')
                    && ($n.op ne 'callmethod')
                    && ($n.op ne 'lexotic')
                    && ($n.op ne 'control')
                    && ($n.op ne 'const')
                    && ($n.name ne '')
                ;
                TreeWalkDo.recurse(:$take);
            },
            -> $n, @p {
                say('>>>remove_bogusOpNames: Op(', $n.dump_extra_node_info, ' ', ~$n.node,')')
                    unless 0 <= nqp::index(
                        'how who inf eqat eqaddr open exit say shift iterator setelems stat exception eoffh closefh setinputlinesep readlinefh flushfh filewritable filereadable backtracestrings getstdout getstderr clone lc join split splice index rindex findcclass findnotcclass decont handle x radix can postinc preinc postdec predec add_n sub_n stringify bind bindkey concat atpos atkey die reprname defor ifnull istype isnull isnull_s iseq_s isne_s iseq_n isgt_n islt_n isle_n isge_n iseq_i isgt_i islt_i isle_i isge_i isconcrete isinvokable isstr isint isnum islist ishash substr falsey if unless for while until elems chars escape list hash iterkey_s iterval existskey existspos numify findmethod getattr bindattr getmessage rethrow cwd getcomp getcurhllsym curlexpad backendconfig',
                        $n.op
                    );
                $n.name(nqp::null_s);
            },
            $ast
        );
    }

    method inline_simple_methods($node) {
        if istype($node, QAST::Node) {

            # first, recurse:
            for $node.list {
                inline_simple_methods($_);
            }

            if istype($node, QAST::Op) && $node.op eq 'callmethod' {
                my $meth := $node.name;
                if $meth {
                    if $meth eq 'push'
                    || $meth eq 'pop'
                    || $meth eq 'shift'
                    || $meth eq 'unshift'
                    {
                        $node.op($meth);
                        $node.name(nqp::null_s);
                    } elsif $meth eq 'key' {
                        $node.op('iterkey_s');
                        $node.name(nqp::null_s);
                    #} elsif $meth eq 'value' { # clashes eg with QAST::SVal.value
                    #    $node.op('iterval');
                    #    $node.name(nqp::null_s);
                    }
                }
            }
            
        }
        
        $node;
    }


    method cloneAndSubst($node, &substitution) {
        nqp::die('cloneAndSubst expects a function as 2nd arg - got ' ~ describe(&substitution) )
            unless nqp::isinvokable(&substitution);
        if istype($node, QAST::Node) {
            
            #return &substitution(nqp::clone($node))    # strange: this actually prevents any recursion...!?!
            #    unless istype($node, QAST::Children);

            $node := $node.shallow_clone;   # also makes a shallow clone of the children's list
            my @children := $node.list;
            my $i := 0;
            for @children {
                my $child := self.cloneAndSubst($_, &substitution);
                unless nqp::isnull($child) {
                    @children[$i] := $child;
                    $i++;
                }
            }
            nqp::setelems(@children, $i);
            
            &substitution($node);
        } else {
            &substitution(nqp::clone($node));
        }
    }

    method collect_params_and_body($node, :$name) {
        nqp::die('expected a QAST::Block - got ' ~ describe($node))
            unless istype($node, QAST::Block);

        my $arity    := 0;
        my %params   := {};
        my %named    := {};
        my %slurpy   := {};
        my %locals   := {};
        my %optional := {};
        my @stmts    := [];

        my @children := nqp::clone($node.list);
        if istype($node[0], QAST::Stmts, QAST::Stmt) {  # replace 1st Stmt(s) with its children
            nqp::splice(@children, $node[0].list, 0, 1);
        }

        for @children {
            if istype($_, QAST::Var) {
                my $varName := $_.name;
                if $_.decl {
                    if $_.decl eq 'param' {
                        %slurpy{$_.name} := $_ if $_.slurpy;
                        %optional{$_.name} := $_ if $_.default;
                        if $_.named {
                            %named{$_.named} := $_;
                        } else {
                            $_.annotate('positional_index', $arity);
                            %params{$varName} := $_;
                            $arity++;
                        }
                    } else {
                        %locals{$varName} := $_;
                    }
                } else {
                    @stmts.push($_);
                }
            } elsif istype($_, QAST::Op) && ($_.op eq 'bind') && istype($_[0], QAST::Var) && $_[0].decl {
                %locals{$_[0].name} := $_[0];
                my $bind := self.cloneAndSubst($_, -> $n { $n });
                $bind[0].decl(nqp::null_s());
                @stmts.push($bind);
            } else {
                @stmts.push($_);
            }
        }
        my %out := nqp::hash( # BEWARE: `hash(:$arity, ..)` might not work!
            'arity', $arity,
            'params', %params,
            'slurpy', %slurpy,
            'named',  %named,
            'locals', %locals,
            'optional', %optional,
            'recursive', 0,
        );
        my $body := %locals
            ?? QAST::Block.new(:blocktype<immediate>, |@stmts)
            !! (@stmts == 1 ?? @stmts[0] !! QAST::Stmts.new(|@stmts));
        %out{'body'} := $body;
        unless nqp::isnull_s($name) {
            TreeWalk.dfs-up(
                -> $n, @p {
                    if istype($n, QAST::Op) && (($n.op eq 'call') || ($n.op eq 'callstatic')) && ($n.name eq $name) {
                        %out{'recursive'} := 1;
                        TreeWalkDo.halt();
                    } else {
                        TreeWalkDo.recurse();
                    }
                },
                -> $n, @p { },
                $body
            );
        }
        %out;
    }

    sub prepare_inliners(@inlinableDefs) {
        my %inliners := {};
        for @inlinableDefs {
            next if nqp::isnull($_);
            nqp::die("invalid def of inlineable sub: " ~ describe($_))
                unless istype($_, QAST::Node);
            nqp::die("invalid def of inlineable sub: " ~ dump($_))
                unless istype($_, QAST::Op) && $_.op eq 'bind'
                    && istype($_[0], QAST::Var)
                    && istype($_[1], QAST::Block);
            my $name   := $_[0].name;
            my $block  := $_[1];
            my %results := collect_params_and_body($block);
            my %params := %results<params>;
            my %named  := %results<named>;
            my %slurpy := %results<slurpy>;
            my %locals := %results<locals>;
            my @optional := %results<optional>;
            my $body   := %results<body>;
            my $arity  := +%params;
            
            if %named {
                my $v := nqp::iterval(nqp::shift(nqp::iterator(%named)));
                nqp::die("cannot handle :named parameters: $name / " ~ dump($v))
            }
            if %slurpy {
                my $v := nqp::iterval(nqp::shift(nqp::iterator(%slurpy)));
                nqp::die("cannot handle :slurpy parameter: $name / " ~ dump($v));
            }
            if %locals {
                my $v := nqp::iterval(nqp::shift(nqp::iterator(%locals)));
                nqp::die('cannot handle :decl(' ~ $v.decl ~ "): $name / " ~ dump($v));
            }
            if @optional {
                my $v := @optional[0];
                nqp::die('cannot handle optional param ' ~ dump($v));
            }

            nqp::die("no statements found in inlineable $name: " ~ dump($block))
                unless !istype($body, QAST::Stmts, QAST::Stmt) || $body.list;

            %inliners{$name} := -> @arguments {
                my $argCount := nqp::elems(@arguments);
                nqp::die("cannot inline call with $argCount args to $arity" ~ "-arity fn $name")
                    unless $argCount == $arity;
                my $out := cloneAndSubst($body, -> $n {
                    if istype($n, QAST::Var) {
                        my $decl := %params{$n.name};
                        if $decl {  # it's a positional arg
                            @arguments[$decl.ann('positional_index')];
                        #} elsif { # TODO: named params
                        } else {
                            $n;
                        }
                    } else {
                        $n;
                    }
                });
                $out;
            };
        }
        %inliners;
    }

    method inline_simple_subs($ast, @inlinableDefs) {
        my %inliners := prepare_inliners(@inlinableDefs);
        TreeWalk.dfs-up(
            -> $n, @p { 
                my $take := istype($n, QAST::Op) 
                    && ($n.op eq 'call' || $n.op eq 'callstatic')
                    && !nqp::isnull_s($n.name) && nqp::existskey(%inliners, $n.name)
                ;
                if $take {
                    $take := $take && !($_.named) for $n.list;
                }
                TreeWalkDo.recurse(:$take);
            },
            -> $n, @p {
                my $out := %inliners{$n.name}($n.list);
                $out.annotate('inlined', $n.name);
                #say('>>>> inlined ', $n.name, dump($out), "\n>>>> for ", dump($n));
                $out.node($n.node);
                if istype($n, QAST::SpecialArg) {
                    $out.flat($n.flat);
                    $out.named($n.named);
                }
                TreeWalk.replace($out);
            },
            $ast
        );
    }


    method renameVars($ast, &map) {
        nqp::die('renameVars expects a QAST::Node as 1st arg - got ' ~ describe($ast) )
            unless istype($ast, QAST::Node);
        nqp::die('renameVars expects a unary fn as 2nd arg - got ' ~ describe(&map) )
            unless nqp::isinvokable(&map);

        TreeWalk.dfs-up(
            -> $n, @p {
                TreeWalkDo.recurse(:take(
                    (    istype($n, QAST::Var)
                      || istype($n, QAST::Op) && ($n.op eq 'call' || $n.op eq 'callstatic')
                    ) && ($n.name ne &map($n.name))
                ));
            },
            -> $n, @p { 
                my $out := $n;
                $out.name(&map($n.name));
                TreeWalk.replace($out);
            },
            $ast
        );
    }


    method isSVal($node) { nqp::istype($node, QAST::SVal) || insist-isa($node, QAST::Node) }
    method isIVal($node) { nqp::istype($node, QAST::IVal) || insist-isa($node, QAST::Node) }
    method isNVal($node) { nqp::istype($node, QAST::NVal) || insist-isa($node, QAST::Node) }

    method isVal($node) { self.isSVal($node) || self.isIVal($node) || self.isNVal($node) }

    method isVar($node) { nqp::istype($node, QAST::Var) || insist-isa($node, QAST::Node) }

    method isOp($node, $opName) {
        #insist-isa($node, QAST::Node);
        insist-isa($opName, str, NO_VALUE);
        nqp::istype($node, QAST::Op) && ($node.op eq ($opName // $node.op))
            || insist-isa($node, QAST::Node);
    }



}   # end of class Util::QAST



sub dump($node, $parent = nqp::null, :$indent = '', :$oneLine = 0) is export {
    Util::QAST.dump($node, $parent, :$indent, :$oneLine);
}

sub qastChildren($ast, *@types)     is export { Util::QAST.qastChildren($ast, |@types) }
sub removeChild($parent, $child)    is export { Util::QAST.removeChild($parent, $child) }
sub findPath(&test, $node, @pathUp = []) is export { Util::QAST.findPath(&test, $node, @pathUp) }

sub findPaths(&test, $ast)              is export { Util::QAST.findPaths(&test, $ast) }
sub fix_var_attrs($ast)                 is export { Util::QAST.fix_var_attrs($ast) }
sub drop_Stmts($ast)                    is export { Util::QAST.drop_Stmts($ast) }
sub replace_assoc_and_pos_scoped($ast)  is export { Util::QAST.replace_assoc_and_pos_scoped($ast) }
sub drop_takeclosure($ast)              is export { Util::QAST.drop_takeclosure($ast) }
sub remove_bogusOpNames($ast)           is export { Util::QAST.remove_bogusOpNames($ast) }
sub renameVars($ast, &map)              is export { Util::QAST.renameVars($ast, &map) }

sub inline_simple_methods($ast)         is export { Util::QAST.inline_simple_methods($ast) }
sub cloneAndSubst($ast, &substitution?) is export { Util::QAST.cloneAndSubst($ast, &substitution // -> $x { $x }) }

sub collect_params_and_body($node, str :$name = nqp::null_s)  is export { Util::QAST.collect_params_and_body($node, :$name) }

sub inline_simple_subs($node, @inlinableDefs) is export { Util::QAST.inline_simple_subs($node, @inlinableDefs) }


sub isSVal($node)                   is export { Util::QAST.isSVal($node) }
sub isIVal($node)                   is export { Util::QAST.isIVal($node) }
sub isNVal($node)                   is export { Util::QAST.isNVal($node) }

sub isVal($node)                    is export { Util::QAST.isVal($node)  }

sub isOp($node, $opName = NO_VALUE) is export { Util::QAST.isOp($node, $opName) }

sub isVar($node)                    is export { Util::QAST.isVar($node) }



sub MAIN(*@ARGS) {
}
