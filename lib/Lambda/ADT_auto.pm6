use v6;


module Lambda::ADT_auto;

role ADT is export {
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