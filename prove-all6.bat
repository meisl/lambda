@echo off

set WHERE=t\%1*.t t\%1**\*.t

REM C:\Perl\bin\prove --state=failed,new,save --color --timer --failures --exec "perl6-m -Ilib" %WHERE%
perl6-m -v & C:\Perl\bin\prove --color --timer --failures --exec "perl6-m -Ilib" %WHERE%

rem parrot-prove doesn't know --recurse - and...
rem ...it simply hangs... :(
rem parrot-prove --merge --failures --exec "perl6 -I ." ./t
