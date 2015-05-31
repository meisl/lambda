use nqp;
use NQPHLL;


sub max($a, $b) is export { $a > $b ?? $a !! $b }
sub min($a, $b) is export { $a < $b ?? $a !! $b }

sub whatsit($v) is export {
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
            @kvs.push(":$k(" ~ whatsit($v) ~ ')');
        }
        return 'hash(' ~ nqp::join(', ', @kvs) ~ ')';
    } elsif nqp::islist($v) {
        my @out := [];
        for $v {
            @out.push(whatsit($_));
        }
        return '[' ~ nqp::join(', ', @out) ~ ']';
    } elsif nqp::istype($v, QAST::Node) {
        my $s := $v.HOW.name($v);
        my $x := $v.dump_extra_node_info;
        return $x ?? "$s($x)" !! $s;
    #} elsif nqp::istype($v, Something) { ??? }
    } elsif nqp::isnull($v) {
        return $reprname;
    } elsif nqp::can($v, 'HOW') && nqp::can($v.HOW, 'name') {
        return $v.HOW.name($v);
    } else {
        return $reprname;
    }
}

sub linesFrom(str $filename, $from = 1, $count?) is export {
    my $to := $from + nqp::defor($count, nqp::inf());
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

sub dump($node, $parent = nqp::null, :$indent = '', :$oneLine = 0) is export {
    my $clsStr := nqp::substr($node.HOW.name($node), 6);
    
    my $isBlockChild := nqp::istype($parent, QAST::Block);
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

    unless nqp::istype($node, QAST::Node) && nqp::defor($node, 0) {
        #nqp::die("cannot dump " ~ whatsit($node));
        if $oneLine {
            return '(' ~ whatsit($node) ~ ')';
        } else {
            return $prefix ~ '► ' ~ whatsit($node);
        }
    }

    my $matchStr := '';
    if $node.node && !istypeAny($node, QAST::Var, QAST::IVal, QAST::NVal, QAST::SVal) {
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
    if nqp::istype($node, QAST::SpecialArg) {
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

    if $clsStr eq 'Op' {
        $extraStr := nqp::substr($extraStr, 1);
        $clsStr := $extraStr;
        $extraStr := '';
        $prefix := $prefix ~ '─';
    } elsif nqp::istype($node, QAST::Var) {
        $clsStr := nqp::istype($node, QAST::VarWithFallback)
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
        if nqp::istype($node, QAST::VarWithFallback) && $node.fallback {
            $specialStr := $specialStr ~ ' :fallback' ~ dump($node.fallback, :oneLine(1));
        }
    } elsif nqp::substr($clsStr, 1, 3) eq 'Val' {
        $prefix := $prefix ~ '◙ ';
        if nqp::istype($node, QAST::SVal) {
            $extraStr := ' "' ~ nqp::escape($node.value) ~ '"';
        } elsif istypeAny($node, QAST::IVal, QAST::NVal) {
            $extraStr := ' ' ~ ~$node.value;
        }
    } elsif $clsStr eq 'Block' {
        $prefix := $prefix ~ '─:';
        my $bt := $node.blocktype;
        if $bt && $bt ne 'declaration' { # don't show default
            $specialStr := $specialStr ~ ' :blocktype(' ~ $bt ~ ')';
        }
    } elsif nqp::substr($clsStr, 0, 4) eq 'Stmt' {
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


# -----------------------------------------------




sub istypeAny($subject, *@types) {
    for @types {
        return 1 if nqp::istype($subject, $_);
    }
    return 0;
}


sub qastChildren($ast, *@types) {
    nqp::die('qastChildren expects a QAST::Node as 1st arg - got ' ~ nqp::reprname($ast) )
        unless nqp::istype($ast, QAST::Node);
    my @out := [];
    if nqp::elems(@types) == 0 {
        @types := [QAST::Node];
    }
    for $ast.list {
        if istypeAny($_, |@types) {
            @out.push($_);
        }
    }
    @out;
}

sub drop_takeclosure($ast) {
    nqp::die('drop_takeclosure expects a QAST::Node - got ' ~ nqp::reprname($ast) )
        unless nqp::istype($ast, QAST::Node);
    if nqp::istype($ast, QAST::Op) && $ast.op eq 'takeclosure' {
        my $child := drop_takeclosure($ast[0]);  # recurse!
        if nqp::istype($ast, QAST::SpecialArg) {
            $child.HOW.mixin($child, QAST::SpecialArg);
            $child.flat($ast.flat);
            $child.named($ast.named);
        }
        $ast := $child;
    #} elsif nqp::istype($ast, QAST::Children) {
    } elsif nqp::can($ast, 'list') { # workaround - not all nodes with children actually do that role
        my @children := [];
        for $ast.list {
            @children.push(drop_takeclosure($_));
        }
        #$ast.set_children(@children);
        my @list := $ast.list;
        while +@list { @list.pop }
        for @children { @list.push($_) }

    }
    $ast;
}

sub _drop_Stmts($ast, $parent) {
    nqp::die('dropStmts expects a QAST::Node - got ' ~ nqp::reprname($ast) ~ (nqp::isstr($ast) ?? ' "' ~ nqp::escape($ast) ~ '"' !! '') )
        unless nqp::istype($ast, QAST::Node);

    if nqp::can($ast, 'resultchild') && nqp::isint($ast.resultchild) {
        return [$ast];   # don't muck with that...
    }

    my @children := [];
    for $ast.list {
        for _drop_Stmts($_, $ast) {
            @children.push($_);
        }
    }
    if nqp::istype($ast, QAST::Stmts)
        && (
              istypeAny($parent, QAST::CompUnit, QAST::Block, QAST::Stmts, QAST::Stmt) 
           || (nqp::elems(@children) < 2)
        )
    {
        return @children; # return the Stmts' children as is, dropping the Stmts node
    } else {
        #$ast.set_children(@children);
        my @list := $ast.list;
        while +@list { @list.pop }
        for @children { @list.push($_) }
    }

    return [$ast];
}

sub drop_Stmts($ast) {
    my @out := _drop_Stmts($ast, nqp::null);
    nqp::elems(@out) == 1
        ?? @out[0]
        !! QAST::Stmts.new(|@out);
}

sub isinResultPosition($node, $parent) {
    my $n := nqp::elems($parent) - 1;
    if ($parent[$n] =:= $node) || (nqp::can($parent, 'resultchild') && $parent[$parent.resultchild] =:= $node) {
        return 1;
    }
    
    while --$n >= 0 {
        return 0 if $node =:= $parent[$n];
    }

    nqp::die(whatsit($node) ~ ' not a child of ' ~ whatsit($parent));
}


sub drop_bogusVars($ast, $parent = nqp::null) {
    if nqp::istype($ast, QAST::Var) && !$ast.decl {
        if istypeAny($parent, QAST::Block, QAST::Stmt, QAST::Stmts) {
            unless isinResultPosition($ast, $parent) {
                #nqp::print(whatsit($parent) ~ ' ' ~ $ast.dump);
                return nqp::null;
            }
        }
    } elsif +$ast.list { # workaround - not all nodes with children actually do that role
        #say('  >> ', whatsit($ast), ' ', nqp::elems($ast.list));
        my @children := [];
        my $changed := 0;
        for $ast.list {
            my $child := drop_bogusVars($_, $ast);
            if nqp::isnull($child) {
                $changed := 1;
            } else {
                @children.push($child);
            }
        }
        if $changed {
            my @list := $ast.list;
            while +@list { @list.pop }
            for @children { @list.push($_) }
        }
    }
    $ast;
}

sub repair_null_decl_attrs_of_vars($ast) {
    nqp::die('remove_bogusOpNames expects a QAST::Node - got ' ~ nqp::reprname($ast) )
        unless nqp::istype($ast, QAST::Node);
    if nqp::istype($ast, QAST::Var) && !$ast.decl {
        $ast.decl(nqp::null_s);
    }
    # recurse in any case, since it could be a VarWithFallback (which does have children)
    for $ast.list {
        repair_null_decl_attrs_of_vars($_);
    }
    $ast;
}

sub remove_bogusOpNames($ast) {
    nqp::die('remove_bogusOpNames expects a QAST::Node - got ' ~ nqp::reprname($ast) )
        unless nqp::istype($ast, QAST::Node);
    if nqp::istype($ast, QAST::Op) && ($ast.op ne 'call') && ($ast.op ne 'callstatic') && ($ast.op ne 'callmethod') && ($ast.op ne 'lexotic') {
        #say('>>>Op(', $ast.op, ' ', $ast.dump_extra_node_info, ')')
        #    unless nqp::index('x radix can postinc preinc add_n sub_n stringify bind bindkey concat atpos atkey die reprname defor isnull iseq_s iseq_n isgt_n islt_n isinvokable isstr isint isnum islist ishash substr if unless for while elems chars escape list hash iterkey_s iterval', $ast.op) >= 0;
        $ast.name(nqp::null_s);
    }
    for $ast.list {
        remove_bogusOpNames($_);
    }
    $ast;
}

sub removeChild($parent, $child) {
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
        nqp::die("could not find child " ~ whatsit($child) ~ ' under ' ~ $parent.dump);
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


sub remove_MAIN($ast) {
    say($ast[0].cuid);
    say("CompUnit load: \n", dump($ast.load));
    say("CompUnit main: \n", dump($ast.main));

    my @path := [];
    my $MAIN := findDef($ast, '&MAIN', @path);
    removeChild(@path[0], $MAIN);
    say(whatsit(@path), "\n", whatsit($MAIN));
    @path := [];
    my $MAINcall := findPath(-> $node, @pathUp {
            if nqp::istype($node, QAST::Op) && ($node.op eq 'call') && ($node.name eq '&MAIN' || (nqp::istype($node[0], QAST::Var) && $node[0].name eq '&MAIN')) {
                my $parent := @pathUp[0];
                if nqp::istype($parent, QAST::Op) && $parent.op eq 'if' {
                    $parent;
                } elsif istypeAny($parent, QAST::Stmt, QAST::Stmts) {
                    $parent := @pathUp[0];
                    if nqp::istype($parent, QAST::Op) && $parent.op eq 'if' {
                        $parent;
                    } else {
                        $node
                    }
                }
            } else {
                $node.list;
            }
        },
        $ast, @path
    );
    removeChild(@path[0], $MAINcall);
    #say(whatsit(@path), ' ', $MAINcall.dump);
    $ast;
}


sub findPath(&test, $node, @pathUp = []) {
    my $res := &test($node, @pathUp);
    if nqp::islist($res) {
        @pathUp.unshift($node);
        for $res {
            my $res2 := findPath(&test, $_, @pathUp);
            return $res2 if $res2;  # ie. if truthy (list, 1 or a node)
        }
        @pathUp.shift();
    } elsif $res {
        if $res =:= $node || !nqp::istype($res, QAST::Node) {    # just truthy to indicate that $node should be returned
            return $node
        } else {
            while !($res =:= @pathUp.shift) {   # eat path up till we find the node
            }
            return $res;
        }
    }
    return nqp::null;
}


sub findDef($ast, $matcher, @pathUp = []) {
    if nqp::isstr($matcher) {
        my $name := $matcher;
        $matcher := -> $var, @pathUp { $var.name eq $name && $var.decl };
    }
    findPath(
        -> $node, @pathUp {
            my $parent := nqp::elems(@pathUp) > 0 ?? @pathUp[0] !! nqp::null;
            if nqp::isnull($parent) || nqp::istype($parent, QAST::CompUnit) {
                $node.list;
            } elsif nqp::istype($parent, QAST::Op) && nqp::istype($node, QAST::Var) {
                 $parent.op eq 'bind' && $matcher($node, @pathUp)
                    ?? $parent
                    !! nqp::null;
            } elsif istypeAny($parent, QAST::Block, QAST::Stmts, QAST::Stmt, QAST::Op) {
                my @next := qastChildren($node, QAST::Block, QAST::Stmts, QAST::Stmt, QAST::Var, QAST::Op); # TODO: put Op nodes first
                @next;
            } else {
                0;
            }
        },
        $ast, @pathUp
    );
}

sub findDefs($ast, $matcher) {
    my @out := [];
    my $current := 1;
    while $current {
        $current := findDef($ast, -> $var, @pathUp {
            my $takeit := 0;
            if $matcher($var, @pathUp) {
                $takeit := 1;
                my $i := nqp::iterator(@out);
                while $i && $takeit {
                    $takeit := !(nqp::shift($i)[0] =:= $var);   # we're storing the parent ('bind')
                }
            }
            $takeit;
        });
        unless nqp::isnull($current) {
#            say(nqp::elems(@out), ': ', dump($current[0], :oneLine));
            @out.push($current);
        }
    }
    @out;
}

sub findValueNodeInHash($keyPredicate, $valuePredicate, $hash = NO_VALUE) is export {
    nqp::die('findValueNodeInHash expects a fn as 1st arg - got ' ~ whatsit($keyPredicate))
        unless nqp::isinvokable($keyPredicate);
    nqp::die('findValueNodeInHash expects a fn as 2nd arg - got ' ~ whatsit($valuePredicate))
        unless nqp::isinvokable($valuePredicate);
    
    if $hash =:= NO_VALUE {
        return -> $hash { findValueNodeInHash($keyPredicate, $valuePredicate, $hash) }
    } elsif !nqp::istype($hash, QAST::Node) {
        nqp::die('findValueNodeInHash expects a fn as (optional) 3rd arg - got ' ~ whatsit($hash));
    }
    my $found := nqp::null;
    if nqp::istype($hash, QAST::Op) && $hash.op eq 'hash' {
        my $it := nqp::iterator($hash.list);
        while $it && !$found {
            my $k := nqp::shift($it);
            if $it && $keyPredicate($k) {
                my $v := nqp::shift($it);
                if $valuePredicate($v) {
                    $found := $v;
                }
            }
        }
    }
    $found;
}

sub cloneAndSubst($node, $substitution) {
    nqp::die('cloneAndSubst expects a QAST::Node as 1st arg - got ' ~ whatsit($node) )
        unless nqp::istype($node, QAST::Node);
    nqp::die('cloneAndSubst expects a function as 2nd arg - got ' ~ whatsit($substitution) )
        unless nqp::isinvokable($substitution);
    
    #return $substitution(nqp::clone($node))    # strange: this actually prevents any recursion...!?!
    #    unless nqp::istype($node, QAST::Children);

    $node := $node.shallow_clone;   # also makes a shallow clone of the children's list
    my @children := $node.list;
    my $i := 0;
    for @children {
        my $child := cloneAndSubst($_, $substitution);
        unless nqp::isnull($child) {
            @children[$i] := $child;
            $i++;
        }
    }
    nqp::setelems(@children, $i);
    
    $substitution($node);
}


sub collect_params_and_body($node, %results = hash(:arity(0), :params({}), :stmts([]))) {
    my $arity  := %results<arity>;
    my %params := %results<params>;
    my @stmts  := %results<stmts>;
    for $node.list {
        if nqp::istype($_, QAST::Var) {
            my $varName := $_.name;
            if $_.decl {
                if $_.decl eq 'param' {
                    nqp::die("cannot handle :named parameter $varName: " ~ dump($_))
                        if $_.named;
                    nqp::die("cannot handle :slurpy parameter $varName: " ~ dump($_))
                        if $_.slurpy;
                    %params{$varName} := $arity;
                    $arity++;
                } else {
                    nqp::die('cannot handle :decl(' ~ $_.decl ~ ')');
                }
            } else {
                @stmts.push($_);
            }
        } else {
            @stmts.push($_);
        }
    }
    %results<arity> := $arity;
    %results;
}


sub inline_simple_subs($node, @inlineDefs, %inlineables = {}) {
    nqp::die('inline_simple_subs expects a QAST::Node as 1st arg - got ' ~ whatsit($node) )
        unless nqp::istype($node, QAST::Node);

    # on first step, prepare:
    if nqp::elems(@inlineDefs) > 0 {
        for @inlineDefs {
            next if nqp::isnull($_);
            nqp::die("invalid def of inlineable sub: " ~ whatsit($_))
                unless nqp::istype($_, QAST::Node);
            nqp::die("invalid def of inlineable sub: " ~ dump($_))
                unless nqp::istype($_, QAST::Op) && $_.op eq 'bind'
                    && nqp::istype($_[0], QAST::Var)
                    && nqp::istype($_[1], QAST::Block);
            my $name   := $_[0].name;
            my $block  := $_[1];
            my %results;
            if istypeAny($block[0], QAST::Stmt, QAST::Stmts) {
                my $it := nqp::iterator($block.list);
                %results := collect_params_and_body(nqp::shift($it));
                while $it {
                    %results := collect_params_and_body(nqp::shift($it), %results);
                }
            } else {
                %results := collect_params_and_body($block);
            }
            my $arity  := %results<arity>;
            my %params := %results<params>;
            my @stmts  := %results<stmts>;


            if nqp::elems(@stmts) == 0 {
                nqp::die("no statements found in inlineable $name: " ~ dump($block));
            } elsif nqp::elems(@stmts) == 1 {
                $block := @stmts[0];
            } else {
                $block := QAST::Stmts.new(|@stmts);
            }

            %inlineables{$name} := -> @arguments {
                my $argCount := nqp::elems(@arguments);
                nqp::die("cannot inline call with $argCount args to $arity" ~ "-arity fn $name")
                    unless $argCount == $arity;
                my $out := cloneAndSubst($block, -> $n {
#                    say('####', dump($n));
                    if nqp::istype($n, QAST::Var) && nqp::existskey(%params, $n.name) {
                        my $out := @arguments[%params{$n.name}];
#                        say('#### substituted ', dump($out, :oneLine), ' for ', dump($n, :oneLine));
                        $out;
                    } else {
                        $n;
                    }
                });
                $out;
            };
        }
        return inline_simple_subs($node, [], %inlineables);
    }

    # next, recurse into children:
    my $i := 0;
    my @children := $node.list;
    for @children {
        @children[$i] := inline_simple_subs($_, [], %inlineables);
        $i++;
    }

    if nqp::istype($node, QAST::Op) && ($node.op eq 'call' || $node.op eq 'callstatic') {
        my $codeMaker := %inlineables{$node.name};
        if $codeMaker {
            my $out := $codeMaker($node.list);
#            say('>>>> inlined ', dump($out), "\n>>>> for ", dump($node));
            $out.node($node.node);
            $out.flat($node.flat);
            $out.named($node.named);
            $node := $out;
        }
    }
    
    $node;
}

sub inline_simple_methods($node) {
    nqp::die('inline_simple_methods expects a QAST::Node - got ' ~ whatsit($node) )
        unless nqp::istype($node, QAST::Node);

    # first, recurse:
    for $node.list {
        inline_simple_methods($_);
    }

    if nqp::istype($node, QAST::Op) && $node.op eq 'callmethod' {
        my $meth := $node.name;
        if $meth {
            if nqp::index('push pop shift unshift', $meth) > -1 {
                $node.op($meth);
                $node.name(nqp::null_s);
            } elsif $meth eq 'key' {
                $node.op('iterkey_s');
                $node.name(nqp::null_s);
            } elsif $meth eq 'value' {
                $node.op('iterval');
                $node.name(nqp::null_s);
            }
        }
    }
    
    $node;
}

sub replace_assoc_and_pos_scoped($node) {
    nqp::die('replace_assoc_and_pos_scoped expects a QAST::Node - got ' ~ whatsit($node) )
        unless nqp::istype($node, QAST::Node);

    # first, recurse:
    my $i := 0;
    my @children := $node.list;
    for @children {
        @children[$i] := replace_assoc_and_pos_scoped($_);
        $i++;
    }

    if nqp::istype($node, QAST::Op) && ($node.op eq 'bind') && !nqp::istype($node[0], QAST::Var) {
        # then our 1st child was just transformed to an 'atkey' or 'atpos'
        my $child1 := $node.shift;
        nqp::die("ooops: " ~ dump($child1, :oneLine))
            unless nqp::istype($child1, QAST::Op);
        my $which := nqp::substr($child1.op, 0, 5); # substr to allow for typed variants _i, _s, etc
        nqp::die("ooops: cannot handle op $which: " ~ dump($child1, :oneLine))
            unless $which eq 'atpos' || $which eq 'atkey';
        $node.op('bind' ~ nqp::substr($child1.op, 2));
        $node.node($child1.node);
        $node.flat($child1.flat);
        $node.named($child1.named);
        $node.unshift($child1[1]);
        $node.unshift($child1[0]);
    } elsif nqp::istype($node, QAST::VarWithFallback) {
        my $fallback := $node.fallback;
        if nqp::isnull($fallback) || istypeAny($fallback, NQPMu) {
            $fallback := nqp::null;
        } else {
            nqp::die('cannot handle fallback ' ~ whatsit($node.fallback))
        }
        my $scope := $node.scope;
        my $op;
        if $scope eq 'positional' {
            $op := 'atpos';
        } elsif $scope eq 'associative' {
            $op := 'atkey';
        }
        if $op {
            $node := QAST::Op.new(:$op,
                :node($node.node),
                :named($node.named),
                :flat($node.flat),
                |$node.list
            );
            #$node := $out;
        }
    }
    $node;
}


sub renameVars($ast, $map?) {
    nqp::die('renameVars expects a QAST::Node as 1st arg - got ' ~ whatsit($ast) )
        unless nqp::istype($ast, QAST::Node);
    if nqp::defined($map) {
        nqp::die('renameVars expects a unary fn as 2nd arg(optional) - got ' ~ whatsit($map) )
            unless nqp::isinvokable($map);
    } else {
        $map := -> str $name { $name };
    }
    if nqp::istype($ast, QAST::Var) 
       || (
          nqp::istype($ast, QAST::Op)
          && (($ast.op eq 'call') || ($ast.op eq 'callstatic'))
        ) {
        my str $old := $ast.name;
        my str $new := $map($old);
        if $new ne $old {
            $ast.name($new);
        }
    }
    #if nqp::istype($ast, QAST::Children) {
    if nqp::can($ast, 'list') { # workaround - not all nodes with children actually do that role
        for $ast.list {
            renameVars($_, $map);
        }
    }
    $ast;
}

# -----------------------------------------------



role StrByDump {
    method Str() { dump(self) }
}

class SmartCompiler is NQP::Compiler {

    method BUILD() {
        # in this order (!):
        self.addstage('ast_save',     :after<ast>);
        #self.addstage('optimize',    :before<ast_save>);

        # Add extra command line options.
        my @clo := self.commandline_options();
        @clo.push('parsetrace');
        @clo.push('setting=s');
        @clo.push('setting-path=s');
        @clo.push('module-path=s');
        @clo.push('no-regex-lib');
        @clo.push('stable-sc');
        @clo.push('optimize=s');
    }

    method log($msg, *@moreMsgPieces) {
        my str $out := '# [' ~ self.compiler_progname ~ '] ' ~ $msg;
        for @moreMsgPieces {
            $out := $out ~ $_;
        }
        say($out);
    }

    method collect_stats($node) {
        my %results := {};
        my sub doit($node) {
            nqp::die("collect_stats expects a QAST::Node - got " ~ whatsit($node))
                unless nqp::istype($node, QAST::Node);

            my $HOWname := $node.HOW.name($node);
    #        %results{$HOWname}++;

            %results<Node>++; # size of tree
            if nqp::istype($node, QAST::Block) {
                %results<Block>++;
            } elsif istypeAny($node, QAST::Stmt, QAST::Stmts) {
                %results<Stmt(s)>++;
            } elsif nqp::istype($node, QAST::Op) {
                my $op := $node.op;
    #            %results{$HOWname ~ '(' ~ $op ~ ')'}++;
                %results<op>++;
                %results<list>++        if  $op eq 'list';
                %results<hash>++        if  $op eq 'hash';
                %results<bind>++        if  $op eq 'bind';
                %results<call>++        if  $op eq 'call';
                %results<callstatic>++  if  $op eq 'callstatic';
                %results<callmethod>++  if  $op eq 'callmethod';
                %results<takeclosure>++ if  $op eq 'takeclosure';
            } elsif nqp::istype($node, QAST::Var) {
                %results<Var>++;
            } elsif nqp::istype($node, QAST::IVal) {
                %results<IVal>++;
            } elsif nqp::istype($node, QAST::NVal) {
                %results<NVal>++;
            } elsif nqp::istype($node, QAST::SVal) {
                %results<SVal>++;
                %results<SValChars> := %results<SValChars> + nqp::chars($node.value);
            }

            for $node.list {
                doit($_);
            }
        }
        doit($node);
        %results<callish> := %results<call> + %results<callstatic> + %results<callmethod>;
        %results<val> := %results<IVal> + %results<NVal> + %results<SVal>;
        %results;
    }

    # override stage 'ast' and make the AST stringifiable
    
    method ast($source, *%adverbs) {
        my $ast := $source.ast();
        self.panic("Unable to obtain AST from " ~ $source.HOW.name($source))
            unless $ast ~~ QAST::Node;
        $ast.HOW.mixin($ast, StrByDump);
        $ast;
    }

    # additional stages

    method ast_clean($ast, *%adverbs) {
        self.log('ast_clean: ', self.user-progname, '...');
        
        $ast := drop_takeclosure($ast);
        
        $ast := drop_Stmts($ast);
        $ast := drop_bogusVars($ast);       # do this *after* drop_Stmts !!!
        $ast := remove_bogusOpNames($ast);
        #$ast := remove_MAIN($ast);
        $ast := repair_null_decl_attrs_of_vars($ast);
        
        # from here it's rather optimization...
        $ast := replace_assoc_and_pos_scoped($ast);
        $ast := inline_simple_methods($ast);

        my @inlinecandidates;
        @inlinecandidates := findDefs($ast, -> $var, @pathUp {
               (nqp::index($var.name, '&STATS_') > -1)
            || (nqp::index($var.name, '&LAMFIELD_') > -1)
            || (nqp::index('&lam2id &lam2code &lam2fvs &int2str &num2str', $var.name) > -1)
        });
        $ast := inline_simple_subs($ast, @inlinecandidates);

        $ast := renameVars($ast, -> $s {
            my str $fst := nqp::substr($s, 0, 1);
            my str $snd := nqp::substr($s, 1, 1);
            $fst eq '&' || $snd eq 'λ'
                ??  '.' ~ nqp::substr($s, 1)
                !! $s;
        });

        $ast;
    }

    method ast_stats($ast, *%adverbs) {
        my %stats := self.collect_stats($ast);

        my @statskeyDefs := findDefs($ast, -> $var, @pathUp {
            nqp::index($var.name, 'STATS_') > -1;
        });
        my @statskeys := [];
        for @statskeyDefs {
            my $v := $_[1][0];
            if istypeAny($v, QAST::SVal, QAST::IVal, QAST::NVal) {
                 @statskeys.push($v.value);
            }
        }

        my sub svalPred($value = NO_VALUE) {
            -> $node { nqp::istype($node, QAST::SVal) && ($value =:= NO_VALUE || $node.value eq $value) }
        }

        my sub ivalPred($value = NO_VALUE) {
            -> $node { nqp::istype($node, QAST::IVal) && ($value =:= NO_VALUE || $node.value == $value) }
        }

        my sub opPred($op = NO_VALUE) {
            -> $node { nqp::istype($node, QAST::Op) && ($op =:= NO_VALUE || $node.op eq $op) }
        }
        

        my $findStatsHash := findValueNodeInHash(svalPred('stats'), opPred('hash'));
        my $infoHashDef := findDef($ast, -> $var, @pathUp {
            if $var.name eq '%info' {
                $findStatsHash(@pathUp[0][1]);
            }
        });
        my $infoHash := $findStatsHash($infoHashDef[1]);
        if $infoHash {
#            say(dump($infoHashDef));
            my $findStatNode := -> $statKey {
                findValueNodeInHash(svalPred($statKey), ivalPred(), $infoHash)
            };
            for @statskeys {
                my $node := $findStatNode($_);
                if $node && nqp::existskey(%stats, $_) {
                    $node.value(%stats{$_});
#                    say(">>>> stat $_ := ", dump($node, :oneLine));
                }
            }
        } else {
            self.log('ast_stats WARNING: no %info hash found in AST of ', self.user-progname);
            self.log('ast_stats WARNING: ...dunno how to insert actual stats - which are:');
            for %stats {
                self.log('    ', nqp::iterkey_s($_), ' = ', nqp::iterval($_))
            }
        }

        $ast;
    }

    method ast_save($ast, *%adverbs) {
        my $qastfileName := self.user-progname ~ '.qast';
        return $ast
            if %adverbs<output> eq $qastfileName;
        spew($qastfileName, ~$ast);
        self.log('ast_save: QAST dump written to ', $qastfileName);
        $ast;
    }

}


my $needsCompilation := 0;

class NQPCompiler is SmartCompiler {

    method BUILD() {
        self.language('nqp');
        self.parsegrammar(NQP::Grammar);
        self.parseactions(NQP::Actions);
        return self;
    }

    method compiler_progname($value = NO_VALUE) { 'nqpc' }

    method handle-exception($error) {
        nqp::rethrow($error);
    }

    method compileFile($file, :$lib = '.', :$target = 'mbc', :$stagestats) {
        my $nqpName := "$lib/$file.nqp";
        #say("<nqpc> $nqpName: target=$target ");
        my $qastName := "$nqpName.qast";
        my $mvmName := "$lib/$file.moarvm";
        if !nqp::filereadable($nqpName) {
            nqp::die("no such file: $nqpName");
        }
        if nqp::stat($mvmName, nqp::const::STAT_EXISTS) && !nqp::filewritable($mvmName) {
            nqp::die("cannot write to file: $mvmName");
        }
        my $nqpTime := nqp::stat($nqpName, nqp::const::STAT_MODIFYTIME);
        my $mvmTime := nqp::filewritable($mvmName)
            ?? nqp::stat($mvmName, nqp::const::STAT_MODIFYTIME)
            !! 0
        ;
        $needsCompilation := 1; #$needsCompilation || ($nqpTime > $mvmTime);
        if !$needsCompilation {
            return nqp::null;   # means: "not compiled (again) because it was up-to-date"
        } else {
            my @opts := [
                '--module-path=' ~ $lib,
            ];
            if $target eq 'mbc' {
                @opts.push('--output=' ~ $mvmName);
            } elsif $target eq 'ast' || $target eq 'ast_clean' || $target eq 'ast_save' {
                @opts.push('--output=' ~ $qastName);    # not only write it but also prevent NQP::Compiler to dump it to stdout and return a null
            }
            my @args := nqp::clone(@opts);
            @args.unshift('nqpc');  # give it a program name (for command_line)
            @args.push($nqpName);
            #say($mvmName, '...');

            self.log('$ ', nqp::join(' ', @args));
            #say(nqp::x('-', 29));
            my $*USER_FILE := $nqpName;
            my $result;
            my $error;
            try {
                $result := self.command_line(@args, 
                    :encoding('utf8'), 
                    :transcode('ascii iso-8859-1'),
                    :$target,
                    :$stagestats
                );
                CATCH {
                    $error := $_;
                }
            }
            unless $error {
                if nqp::isnull($result) {   # returning non-null means: "yes, we did compile and write it to disk"
                    if $target eq 'mbc' {
                        $result := $mvmName;
                    } else {
                        nqp::die("??? - successfully compiled $nqpName to target $target - but got null result...!?");
                    }
                }
                return $result;
            }
            
            my $msg := nqp::getmessage($error);
            my $msglc := nqp::lc($msg);
            my $from;
            my $to;
            if nqp::index($msglc, 'no such file') > -1 {
                $from := nqp::index($msglc, '\'') + 1;
                $to   := nqp::index($msglc, '\'', $from);
                my $file := nqp::substr($msg, $from, $to - $from);
                say('Error: missing module "', $file ~ '"');
            } elsif nqp::index($msglc, 'unable to write bytecode') > -1 {
                $from := nqp::index($msglc, '\'') + 1;
                $to   := nqp::index($msglc, '\'', $from);
                my $file := nqp::substr($msg, $from, $to - $from);
                my $line := 1;
                $msg := nqp::join('', [
                          'Error: ', $msg,
                    "\n", '  at ', $nqpName, ':', ~$line,
                    "\n"
                ]);
            } elsif nqp::index($msglc, 'confused') > -1 {
                $from := nqp::index($msglc, 'at line') + 1;
                $from := nqp::findcclass(nqp::const::CCLASS_NUMERIC, $msglc, $from, nqp::chars($msglc) - $from);
                $to   := nqp::findnotcclass(nqp::const::CCLASS_NUMERIC, $msglc, $from, nqp::chars($msglc) - $from);
                my $line := nqp::substr($msg, $from, $to - $from);
                $line := max(1, $line - 1);
                $msg := nqp::substr($msg, 0, $from) ~ $line ~ nqp::substr($msg, $to);
                $msg := nqp::join('', [
                          'Error: ', $msg,
                    "\n", '  at ', $nqpName, ':', ~$line,
                    "\n"
                ]);
            } elsif nqp::index($msglc, 'assignment ("=") not supported ') > -1 {
                $from := nqp::index($msglc, 'at line') + 1;
                $from := nqp::findcclass(nqp::const::CCLASS_NUMERIC, $msglc, $from, nqp::chars($msglc) - $from);
                $to   := nqp::findnotcclass(nqp::const::CCLASS_NUMERIC, $msglc, $from, nqp::chars($msglc) - $from);
                my $line := nqp::substr($msg, $from, $to - $from);
                $line := max(1, $line - 1);
                my @lines := linesFrom($nqpName, $line, 2);
                my $i := 0;
                my $n := nqp::elems(@lines);
                my $column;
                while $i < $n {
                    my $line := @lines[$i];
                    my $at := nqp::index($line, '=');
                    if $at > -1 {
                        $column := $at + 1;
                        $i := $n;   # exit loop
                    } else {
                        $i++;
                        $line++;
                    }
                }
                $msg := nqp::substr($msg, 0, $from) ~ $line ~ nqp::substr($msg, $to);
                $msg := nqp::join('', [
                          'Error: ', $msg,
                    "\n", '   at ', $nqpName, ':', ~$line, ($column ?? ':' ~ $column !! ''),
                    "\n",
               ]);
            # TODO: Unable to parse expression in blockoid; couldn't find final '}'  at line 143, near "$msg := $m"
            # TODO: Use of undeclared variable '$fuck' at line 4, near " := [a b];"
            # TODO: Malformed binding at line 4, near "[a b];\ngra"
            } elsif 0 {
                my $line := 1;
                my $column;
                $msg := nqp::join('', [
                          'ERROR: ', $msg,
                    "\n", '   at ', $nqpName, ':', ~$line, ($column ?? ':' ~ $column !! ''),
                    "\n",
               ]);
            } else {
                $msg := $msg ~ nqp::join("\n", nqp::backtracestrings($error));
            }
            nqp::flushfh(nqp::getstdout());
            nqp::die($msg);
        }
    }

}



sub MAIN(*@ARGS) {
    my $cwd := nqp::cwd();
    my $lib;
    my $ext := '.nqp';
    my $sep := nqp::x('-', 29);
    my $nqpc := NQPCompiler.new();
    my %opts := hash();

    @ARGS.shift;  # first is program name

    if nqp::elems(@ARGS) == 0 {
        #@ARGS.push('LGrammar');
        #@ARGS.push('LActions');
        #@ARGS.push('L');

        @ARGS.push('runtime');
        $nqpc.addstage('ast_clean', :before<ast_save>);
        $nqpc.addstage('ast_stats', :before<ast_save>);
        %opts<stagestats> := 1;
        %opts<target>     := '';    # ...and run it
    }


    for @ARGS {
        my $file := $_ ~ $ext;
        
        # XXX FIXME: lib
           if $_ eq 'nqpc'      { $lib := '.' }
        elsif $_ eq 'testing'   { $lib := 'lib' }
        else {
            $lib := 'lib/L'
        }
        
        my $result := $nqpc.compileFile($_, :$lib,  |%opts);
        if nqp::isnull($result) {
            $nqpc.log("uptodate: $lib/$file");
        } else {
            $nqpc.log("compiled: $lib/$file ~> " ~ whatsit($result));
        }
        CATCH {
            $nqpc.log("ERROR: $lib/$file");
            $nqpc.log($sep);
            $nqpc.log("  CWD: $cwd");
            $nqpc.log("  lib: $lib");
            $nqpc.log(' ARGS: ', nqp::join(' ', @ARGS));
            $nqpc.log('');
            $nqpc.log(~$_);
            nqp::exit(1);
            
            #nqp::die($msg);    # cannot do this: sometimes "Memory allocation failed; could not allocate zu bytes"
        }
    }
    say($sep);
}

