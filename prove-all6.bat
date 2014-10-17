@echo off
C:\Perl\bin\prove --state=failed,fresh --color --failures --recurse --exec "perl6-m -I lib" ./t

rem parrot-prove doesn't know --recurse - and...
rem ...it simply hangs... :(
rem parrot-prove --merge --failures --exec "perl6 -I ." ./t