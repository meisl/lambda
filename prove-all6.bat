@echo off
C:\Perl\bin\prove --state=failed,save --color --timer --failures --exec "perl6-m -Ilib" %*

rem parrot-prove doesn't know --recurse - and...
rem ...it simply hangs... :(
rem parrot-prove --merge --failures --exec "perl6 -I ." ./t