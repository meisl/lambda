@echo off

SET RAKUDO=C:\rakudo
SET NQPLIB=%RAKUDO%\languages\nqp\lib
SET MOAR=%RAKUDO%\bin\moar.exe --libpath="%NQPLIB%"
SET NQP=%MOAR% "%NQPLIB%\nqp.moarvm"

REM don't need this since ModuleLoader automatically searches . and ./blib
REM SET MYLIBS="blib"

SET NQPC=%MOAR% "blib\nqpc.moarvm"

CALL %NQP% lib\nqpc-bootstrap.nqp
IF %ERRORLEVEL% GEQ 1 GOTO :EOF
%NQPC% %*
