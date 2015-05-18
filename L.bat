@ echo off

REM echo compiling LGrammar...
REM call nqp-m.bat --module-path=lib/L --target=mbc --output=lib/L/LGrammar.moarvm lib/L/LGrammar.nqp

REM echo compiling L...
REM call nqp-m.bat --module-path=lib/L --target=mbc --output=lib/L/L.moarvm lib/L/L.nqp

REM echo compiling and running L...
REM call nqp-m.bat --module-path=lib/L lib/L/L.nqp %*

call nqp-m.bat nqpc.nqp LGrammar LActions L
moar.exe --libpath="C:\rakudo\languages\nqp\lib" --libpath="lib\L" "lib\L\L.moarvm" %*
