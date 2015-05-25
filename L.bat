@ echo off

SET OPTS=
IF x%~x1 EQU x.L (
    SET OPTS=
    SET IN=%~dpnx1
) ELSE (
    SET OPTS=%1
    IF x%~x2 EQU x.L (
        SET OPTS=%1
        SET IN=%~dpnx2
    ) ELSE (
        SET OPTS=%1 %2
        IF x%~x3 EQU x.L (
            SET OPTS=%1 %2
            SET IN=%~dpnx3
        ) ELSE (
            IF x%~x4 EQU x.L (
                SET OPTS=%1 %2 %3
                SET IN=%~dpnx4
            ) ELSE (
                IF x%~x5 EQU x.L (
                    SET OPTS=%1 %2 %3 %4
                    SET IN=%~dpnx5
                ) ELSE (
                    IF x%~x6 EQU x.L (
                        SET OPTS=%1 %2 %3 %4 %5
                        SET IN=%~dpnx6
                    ) ELSE (
                        ECHO could not find input .L file
                        ECHO arguments: %*
                        EXIT /B 1
                    )
                )
            )
        )
    )
)

SET QASTOUT=%IN%.qast
SET PROGOUT=%IN%.out
SET NQPLIB=C:\rakudo\languages\nqp\lib
SET MOAR=moar.exe --libpath="%NQPLIB%"
SET NQPCARGS=nqpc LGrammar LActions L
SET COMPILECOMPILER=%MOAR% "%NQPLIB%\nqp.moarvm" nqpc.nqp %NQPCARGS%
SET COMPILECOMPILEROUT=nqpc.out
SET L=%MOAR% --libpath="lib\L" --libpath="." "lib\L\L.moarvm"

REM echo OPTS: %OPTS%
REM echo IN: %IN%
REM echo QASTOUT: %QASTOUT%
REM echo PROGOUT: %PROGOUT%

REM ECHO $ %COMPILECOMPILER%
ECHO #$ nqpc %NQPCARGS%
%COMPILECOMPILER% >%COMPILECOMPILEROUT% 2>&1
IF %ERRORLEVEL% GEQ 1 (
    REM ECHO ERRORLEVEL: %COMPILERESULT%
    TYPE %COMPILECOMPILEROUT%
    GOTO :ERROR
)

IF x%OPTS% EQU x (
    GOTO :RUNIT
) ELSE (
    IF x%OPTS% EQU x"--target=ast" (
        GOTO :QASTONLY
    ) ELSE (
        ECHO Sorry, do not understand options %OPTS%
        GOTO :DONE
    )
)


:RUNIT
COPY /Y %COMPILECOMPILEROUT% %PROGOUT% >NUL
ECHO #$ L %IN%
%L% %IN% >>%PROGOUT% 2>&1
IF %ERRORLEVEL% GEQ 1 (
    REM ECHO ERRORLEVEL: %ERRORLEVEL%
    TYPE %PROGOUT%
    GOTO :ERROR
)
TYPE %PROGOUT%
GOTO :DONE


:QASTONLY
ECHO NOTE: L automatically saves the QAST to xyz.L.qast - just run it...
GOTO :ERROR


:DONE
DEL %COMPILECOMPILEROUT%
EXIT /B 0


:ERROR
DEL %COMPILECOMPILEROUT%
EXIT /B 1
