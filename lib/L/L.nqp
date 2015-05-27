use NQPHLL;

use LGrammar;
use LActions;
use nqpc;


class LCompiler is SmartCompiler {

    method BUILD() {
        self.language('lambda');
        self.parsegrammar(LGrammar);
        self.parseactions(LActions.new);
        
        self.addstage('mkRuntime', :after<start>);
        return self;
    }

    method mkRuntime($src) {
        my $nqpc := NQPCompiler.new();
        my $rtQAST := $nqpc.compileFile('runTime', :lib('lib/L'), :target('saveast'));
        say("# [Lc] mkRuntime ~> " ~ whatsit($rtQAST));
        return $src;
    }


    method command_line(@args, *%adverbs) {
        my $program-name := @args[0];
        my $res  := self.process_args(@args);
        my %opts := $res.options;
        my @a    := $res.arguments;
        nqp::die('no input file specified')
            unless nqp::elems(@a) > 0;
        nqp::die('cannot (yet) handle more than one input file: ' ~ nqp::join('; ', @a))
            unless nqp::elems(@a) <= 1;

        for %opts {
            %adverbs{$_.key} := $_.value;
        }
        self.usage($program-name) if %adverbs<help>  || %adverbs<h>;
        
        #if $!backend.is_precomp_stage(%adverbs<target>) {
        #    %adverbs<precomp> := 1;
        #}

        #self.command_eval(|@a, |%adverbs);
        
        my $*USER_FILE := @a[0];
        my $error := 0;
        my $result;
        try {
            $result := self.evalfiles($*USER_FILE, :encoding('utf8'), |%adverbs);
            CATCH {
                $error := $_;
            }
        }
        if $error {
            nqp::die(">>>Error evaluating $*USER_FILE:\n" ~ $error);
        } else {
            self.interactive_result($result);
        }
    }

}


sub flatten($args) {
    return [$args]
        unless nqp::islist($args);
    my @out := [];
    for $args -> $_ {
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

    my @as := flatten(@ARGS);
    @as.push('Lc')     unless nqp::elems(@as) > 0; # program name for command_line
    @as.push('test.L') unless nqp::elems(@as) > 1;

    $c.command_line(@as, :encoding('utf8'), :stagestats);
}

