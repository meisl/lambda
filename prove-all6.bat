@echo off
C:\Perl\bin\prove --state=failed,new,save --color --timer --failures --exec "perl6-m -Ilib" t\*.t t\**\*.t %*

rem parrot-prove doesn't know --recurse - and...
rem ...it simply hangs... :(
rem parrot-prove --merge --failures --exec "perl6 -I ." ./t