@echo off

CALL nqpc.bat lib\L\L.nqp
IF %ERRORLEVEL% GEQ 1 GOTO :EOF

SET RAKUDO=C:\rakudo
SET NQPLIB=%RAKUDO%\share\nqp\lib
SET MOAR=%RAKUDO%\bin\moar.exe --libpath="%NQPLIB%"

SET L=%MOAR% "blib\L\L.moarvm"

%L% %*
