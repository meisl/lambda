use NQPHLL;

use L::LGrammar;
use L::LActions;
use nqpc;
use Util;
use Util::QAST;


my class NO_VALUE {}


class LCompiler is SmartCompiler {

    has $!runtime;

    method BUILD() {
        self.config<version> := '0.0.1';
        self.language('L');
        self.parsegrammar(LGrammar);
        self.parseactions(LActions.new);
        
        self.addstage('inline_subs', :before<ast_save>);
        self.addstage('marryRT',     :before<ast_save>);
        
        $!runtime := self.mkRuntime;
        
        self.interactive_command('!h', -> :$in, :$out {
                nqp::sayfh($out, '  !h    - this help');
                nqp::sayfh($out, '  !q    - quit');
                nqp::sayfh($out, '  "foo" - string literal');
                nqp::sayfh($out, '  \x.x  - lambda abstraction');
                nqp::sayfh($out, '  (x y) - application');
                nqp::sayfh($out, '  (def ((K \x.\_.x) (S \f.\g.\x.f x (g x)) (I (S K K))) I K) - let-like bindings');
        });

        self.interactive_command('!q', -> :$in, :$out { nqp::sayfh($out, 'Bye!'); nqp::exit(0) } );

        return self;
    
    }

    method mkRuntime() {
        my $nqpc := NQPCompiler.new();
        $nqpc.addstage('ast_clean',     :before<ast_save>) unless $nqpc.exists_stage('ast_clean');
        $nqpc.addstage('inline_subs',   :before<ast_save>) unless $nqpc.exists_stage('inline_subs');
        $nqpc.addstage('ast_stats',     :before<ast_save>) unless $nqpc.exists_stage('ast_stats');
        my $runtimeAST := $nqpc.compileFile('lib/L/runTime.nqp', :lib('lib/L'), :target('ast_save'));
        $runtimeAST;
    }

    method compiler_progname($value = NO_VALUE) { 'Lc' }

    method runtime() {
        cloneAndSubst($!runtime);
    }

    # additional stages

    method marryRT($ast, *%adverbs) {
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
        #try {
            $result := self.evalfiles($*USER_FILE, :encoding('utf8'), |%adverbs);
        #    CATCH {
        #        $error := $_;
        #    }
        #}
        if $error {
            nqp::die(">>>Error evaluating $*USER_FILE:\n" ~ $error);
        } elsif nqp::isstr($result) {
            say($result);
        } else {
            say(describe($result));
        }
    }

    method interactive_banner() {
        my $backver := self.backend.version_string;
          'This is the REPL of ' ~ self.version_string ~ " built on $backver\n"
        ~ "type '!h' for for help\n"
        ~ "----------------------\n";
    }


}




sub MAIN(*@ARGS) {
    my $c := LCompiler.new();
    @ARGS := flatten(@ARGS, :map(&unixify));    # nqp itself doesn't seem to get it right (but moarvm does)
    say(describe(@ARGS));
    if nqp::elems(@ARGS) > 1 {  # 1st arg is program name
        #$c.log_level('INFO');
        $c.command_line(@ARGS, :encoding('utf8'), :stagestats);
    } else {
        $c.removestage('ast_save');
        $c.interactive();
    }
}

