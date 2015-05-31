@echo off
SET NQPLIB=--libpath="C:\rakudo\languages\nqp\lib"
SET MYLIBS=--libpath="." --libpath="lib" --libpath="lib\L"
SET NQP="C:\rakudo\languages\nqp\lib\nqp.moarvm"
moar.exe %NQPLIB% %MYLIBS% %NQP% nqpc.nqp %*
