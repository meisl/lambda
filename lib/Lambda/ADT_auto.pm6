use v6;


module Lambda::ADT_auto;


role ADT is export {
    method repr { ... }
}

class ADTRepr is export { ... }

class Ctor is export {
    has ADTRepr:D $.ADT;
    has Int:D     $.nr;
    has Str:D     $.name;
    has Int:D     $.arity;
}

class ADTRepr is export {
    has ADT:U $.p6Type;
    has       @.ctors;

    method new(ADT:U $p6Type, *%ctorSpec) {
        die "need at least one constructor spec (as name => arity mapping)"
            unless %ctorSpec.elems > 0;
        self.bless(:$p6Type, :%ctorSpec);
    }

    method name { $!p6Type.perl }

    submethod BUILD(:$!p6Type, :%ctorSpec) {
        my $i = 1;
        @!ctors = %ctorSpec.map(-> (:$key, :$value) {
            Ctor.new(:ADT(self), :nr($i++), :name($key), :arity($value))
        });
    }
    
    method perl { # must intercept this since it's a cyclic data structure
        return "ADTRepr.new({$!p6Type.perl}, " ~ @!ctors.map(-> $c { "{$c.name} => {$c.arity}" }).join(', ') ~ ')';
    }

}


sub makeMatcher(ADT:U ::T) is export {
    my @ctors = T.repr.ctors;

    my Str $adtName_literal  = T.repr.name;
    my Str $adtName_symbolic = 'S';
    my \S := T;

    my Str $instanceName = '$instance';

    my sub callbackName(Int:D $ctorNr) { "\$on{$ctorNr}" }

    my @callbacks = @ctors.map(-> Ctor $ctor { callbackName($ctor.nr) });

    my Str $instanceApp = $instanceName ~ '(' ~ @callbacks.join(', ') ~ ')';

    my Str $allCtorsSig = @ctors.map(-> Ctor $ctor {
        ":{$ctor.name}(" ~ callbackName($ctor.nr) ~ ')!'
    }).join(', ');


    # -----------------------------------------------------------------------------------------------

    my sub firstLine(Str:D $adtName) {
        "class {$adtName}Matcher does Callable \{\n";
    }

    my sub rest(Str:D $adtName) {
        my $instanceSig = "{$adtName}:D {$instanceName}";
        return qq:to/ENDOFSOURCE/
    # we're getting a capture, so that's why the whole sig is wrapped in parens
    multi method postcircumfix:<( )>(({$instanceSig}, {$allCtorsSig})) \{
        #say ">>>{$adtName_literal} got called with: " ~ \$instance;
        {$instanceApp}
    \}
    
    # fallback to give error message, if none of the other signatures matches
    multi method postcircumfix:<( )>(\$args) \{  # we're getting a capture - always...
        if (\$args.list[0] ~~ {$adtName}) \{
            die 'cannot apply match({$adtName_literal}:D, ...) to ' ~ \$args.gist;
        \} else \{
            die 'expected {$adtName_literal} instance as 1st arg to match({$adtName_literal}:D, ...) - got ' ~ \$args.list[0].gist;
        \}
    \}
\}
ENDOFSOURCE
    }

    # -----------------------------------------------------------------------------------------------


    my $src = firstLine($adtName_literal)
        ~ '    method perl {' ~ "\n"
        ~ '        q:to/ENDOFSOURCE/' ~ "\n"
        ~ firstLine($adtName_literal) ~ "\n"
        ~ '    method perl { ... } # well, cannot repeat this forever...' ~ "\n\n"
        ~ rest($adtName_literal)
        ~ 'ENDOFSOURCE' ~ "\n"
        ~ '    } # end of method `perl`' ~ "\n\n"
        ~ rest($adtName_symbolic)
    ;
    #say ">>>> {$adtName_literal}: $src\n<<<<";

    return EVAL($src);
}
