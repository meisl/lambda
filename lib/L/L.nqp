use NQPHLL;

use L::LGrammar;
use L::LActions;
use nqpc;
use Util;


class LCompiler is SmartCompiler {

    has $!runtime;

    method BUILD() {
        self.language('lambda');
        self.parsegrammar(LGrammar);
        self.parseactions(LActions.new);
        
        self.addstage('mkRuntime',   :after<start>);
        self.addstage('inline_subs', :before<ast_save>);
        self.addstage('marryRT',     :before<ast_save>);
        return self;
    }

    method compiler_progname($value = NO_VALUE) { 'Lc' }

    method runtime($value = NO_VALUE) {
        $!runtime := $value unless $value =:= NO_VALUE;
        $!runtime;
    }
    

    # override stage 'start' in order to reset things
    
    method start($src, *%adverbs) {
        self.runtime(nqp::null);
        $src;
    }

    # additional stages

    method mkRuntime($src) {
        my $nqpc := NQPCompiler.new();
        $nqpc.addstage('ast_clean',     :before<ast_save>);
        $nqpc.addstage('inline_subs',   :before<ast_save>);
        $nqpc.addstage('ast_stats',     :before<ast_save>);
        my $runtimeAST := $nqpc.compileFile('lib/L/runTime.nqp', :lib('lib/L'), :target('ast_save'));
        self.log('mkRuntime: ~> ', describe($runtimeAST));
        self.runtime($runtimeAST);
        return $src;
    }

    method marryRT($ast) {
        my $rt := self.runtime;
        unless nqp::istype($rt, QAST::Node) {
            self.panic("invalid runtime: " ~ describe($rt));
        }
        self.log('marryRT: ', describe($rt));
        
        #my 
        return $ast;
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
        } elsif nqp::isstr($result) {
            say($result);
        } else {
            say(describe($result));
        }
    }

}


sub MAIN(*@ARGS) {
    my $c := LCompiler.new();

    my @as := @ARGS;
    @as.push('Lc')     unless nqp::elems(@as) > 0; # program name for command_line
    @as.push('test.L') unless nqp::elems(@as) > 1;

    $c.command_line(@as, :encoding('utf8'), :stagestats);
}

