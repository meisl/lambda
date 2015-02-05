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


sub makeMatcher(ADT:U $adtTypeObject) is export {
    my ADTRepr $adt = $adtTypeObject.repr;

    my Str $instanceName = '$instance';
    my Str $instanceSig = "{$adt.name}:D {$instanceName}";

    my sub callbackName(Int:D $ctorNr) { "\$on{$ctorNr}" }

    my @callbacks = $adt.ctors.map(-> Ctor $ctor { callbackName($ctor.nr) });

    my Str $instanceApp = $instanceName ~ '(' ~ @callbacks.join(', ') ~ ')';
    #say ">>> {$adt.name}: $instanceApp";

    my Str $allCtorsSig = $adt.ctors.map(-> Ctor $ctor {
        ":{$ctor.name}(" ~ callbackName($ctor.nr) ~ ')!'
    }).join(', ');
    #say ">>>{$adt.name} allCtorsSig: $allCtorsSig";


    # -----------------------------------------------------------------------------------------------

    my Str $firstLine = "class {$adt.name}Matcher does Callable \{\n";
    
    my Str $rest = qq:to/ENDOFSOURCE/
    # we're getting a capture, so that's why the whole sig is wrapped in parens
    multi method postcircumfix:<( )>(  ( {$adt.name}:D \$instance, {$allCtorsSig} )  ) \{
        #say ">>>{$adt.name} got called with: " ~ \$instance;
        {$instanceApp}
    \}
    
    # fallback to give error message, if none of the other signatures matches
    multi method postcircumfix:<( )>(\$args) \{  # we're getting a capture - always...
        if \$args.list[0] !~~ {$adt.name}:D \{
            die 'expected {$adt.name} instance as 1st arg to match({$adt.name}:D, ...) - got ' ~ \$args.list[0].gist;
        \} else \{
            die 'cannot apply match({$adt.name}:D, ...) to ' ~ \$args.gist;
        \}
    \}
\}
ENDOFSOURCE
;

    # -----------------------------------------------------------------------------------------------


    my $src = $firstLine 
        ~ '    method perl {' ~ "\n"
        ~ '        q:to/ENDOFSOURCE/' ~ "\n"
        ~ $firstLine ~ "\n"
        ~ '    method perl { ... } # well, cannot repeat this forever...' ~ "\n\n"
        ~ $rest
        ~ 'ENDOFSOURCE' ~ "\n"
        ~ '    } # end of method `perl`' ~ "\n\n"
        ~ $rest
    ;
    #say '>>>> ' ~ $adt ~ ': ' ~ $src;
    #say '<<<<';
    my $result = EVAL($src);

    return $result;
}


#`{

my role TFoo {};

my $x = 7 does TFoo;
my $y = 9 does TFoo;

constant &matchFoo is export = #EVAL q:to/ENDOFEVAL/
    class {
        multi method postcircumfix:<( )>((Int $x)) {
            say 'postcircumfix:<( )>(Int) called: ' ~ $x;
        }
        multi method postcircumfix:<( )>((TFoo:D $x, TFoo:D $y)) {
            say 'postcircumfix:<( )>(TFoo TFoo) called: ' ~ "$x, $y";
        }
        multi method postcircumfix:<( )>($args) {
            say 'fallback postcircumfix:<( )> called: ' ~ $args.perl;
        }
    };
#ENDOFEVAL
;


    say &matchFoo.perl;
    say '';
    matchFoo();
    matchFoo(5);
    matchFoo($x);
    matchFoo($x, $y);
}