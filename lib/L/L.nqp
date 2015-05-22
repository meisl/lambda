use NQPHLL;

use LGrammar;
use LActions;


class LCompiler is HLL::Compiler {
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

    method inspectQAST($ast) {
        my $fileName := $*USER_FILES;
        my $outfileName := $fileName ~ '.qast';
        #say('>>>Lc.inspectQAST: ->"', $outfileName, '"');
        my $outfile := nqp::open($outfileName, 'w');
        nqp::printfh($outfile, $ast.dump);
        nqp::closefh($outfile);
        return $ast;
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
    $c.addstage('inspectQAST', :after<ast>);
    $c.command_line(flatten(@ARGS), :encoding('utf8'));
}

