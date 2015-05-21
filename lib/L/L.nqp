use NQPHLL;

use LGrammar;
use LActions;


class LCompiler is HLL::Compiler {
    method command_line(@args, *%adverbs) {
        my $program-name := @args[0];
        my $res  := self.process_args(@args);
        my %opts := $res.options;
        my @a    := $res.arguments;

        for %opts {
            %adverbs{$_.key} := $_.value;
        }
        self.usage($program-name) if %adverbs<help>  || %adverbs<h>;
        
        #if $!backend.is_precomp_stage(%adverbs<target>) {
        #    %adverbs<precomp> := 1;
        #}

        #self.command_eval(|@a, |%adverbs);
        
        my $*USER_FILES := join('; ', @a);
        my $error := 0;
        my $result;
        try {
            $result := self.evalfiles(|@a, :encoding('utf8'), |%adverbs);
            CATCH {
                $error := $_;
            }
        }
        if $error {
            nqp::die(">>>Error evaluating $*USER_FILES:\n" ~ $error);
        } else {
            self.interactive_result($result);
        }
    }
}



sub flatten(@args) {
    my @out := [];
    for @args -> $_ {
        if nqp::islist($_) {
            for flatten($_) -> $_ {
                @out.push($_);
            }
        } else {
            @out.push($_);
        }
    }
    @out;
}

sub MAIN(@ARGS) {
    my $c := LCompiler.new();
    $c.language('lambda');
    $c.parsegrammar(LGrammar);
    $c.parseactions(LActions.new);
    $c.command_line(flatten(@ARGS), :encoding('utf8'));
}

