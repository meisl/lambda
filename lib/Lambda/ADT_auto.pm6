use v6;


module Lambda::ADT_auto;


role ADT is export {
    method repr { ... }
}

class ADTRepr is export { ... }

class Ctor is export {
    has ADTRepr:D $.ADT;
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
        @!ctors = %ctorSpec.map(-> (:$key, :$value) {
            Ctor.new(:ADT(self), :name($key), :arity($value))
        });
    }
    
    method perl { # must intercept this since it's a cyclic data structure
        return "ADTRepr.new({$!p6Type.perl}, " ~ @!ctors.map(-> $c { "{$c.name} => {$c.arity}" }).join(', ') ~ ')';
    }

}


sub makeMatcher(ADT:U $adtTypeObject) is export {
    my Str $adt = $adtTypeObject.perl;
    my Str $src = qq:to/ENDOFSOURCE/
class {$adt}Matcher is GotPerlSrc does Callable \{    
    multi method postcircumfix:<( )>(\$args) \{  # we're getting a capture - always...
        if \$args.list[0] !~~ $adt:D \{
            die 'cannot apply match($adt:D, ...) to ' ~ \$args.list[0].gist;
        \} else \{
            die 'cannot apply match($adt:D, ...) to ' ~ \$args.gist;
        \}
    \}
\}
ENDOFSOURCE
;

    my class GotPerlSrc {
        method perl { $src }
    };
    my $result = EVAL($src);
    return $result;
}

#`{
constant &matchFoo is export = #EVAL q:to/ENDOFEVAL/
    class {
        multi method postcircumfix:<( )>((Int $x)) {
            say 'postcircumfix:<( )>(Int) called: ' ~ $x;
        }
        multi method postcircumfix:<( )>((TFoo $x, TFoo $y)) {
            say 'postcircumfix:<( )>(TFoo TFoo) called: ' ~ "$x, $y";
        }
    };
#ENDOFEVAL
;


    say &matchTerm.perl;
    say '';
    matchTerm();
    matchTerm(5);
    matchTerm($x);
    matchTerm($x, $y);
}