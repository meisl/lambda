@ echo off

SET OPTS=
IF x%~x1 EQU x.L (
    SET OPTS=
    SET IN=%~dpn1
) ELSE (
    SET OPTS=%1
    IF x%~x2 EQU x.L (
        SET OPTS=%1
        SET IN=%~dpn2
    ) ELSE (
        SET OPTS=%1 %2
        IF x%~x3 EQU x.L (
            SET OPTS=%1 %2
            SET IN=%~dpn3
        ) ELSE (
            IF x%~x4 EQU x.L (
                SET OPTS=%1 %2 %3
                SET IN=%~dpn4
            ) ELSE (
                IF x%~x5 EQU x.L (
                    SET OPTS=%1 %2 %3 %4
                    SET IN=%~dpn5
                ) ELSE (
                    IF x%~x6 EQU x.L (
                        SET OPTS=%1 %2 %3 %4 %5
                        SET IN=%~dpn6
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
SET COMPILECOMPILER=%MOAR% "%NQPLIB%\nqp.moarvm" nqpc.nqp LGrammar LActions L
SET L=%MOAR% --libpath="lib\L" "lib\L\L.moarvm"

REM echo OPTS: %OPTS%
REM echo IN: %IN%
REM echo QASTOUT: %QASTOUT%
REM echo PROGOUT: %PROGOUT%

ECHO $ %COMPILECOMPILER%
%COMPILECOMPILER% >L.stdout.tmp
SET COMPILERESULT=%ERRORLEVEL%
REM must save this *immediately*!

IF NOT x%COMPILERESULT%==x0 (
    ECHO ERRORLEVEL: %COMPILERESULT%
    TYPE L.stdout.tmp
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
COPY /Y L.stdout.tmp %QASTOUT% >NUL
ECHO $ %L% %IN%.L
%L% --target=ast %IN%.L >>%QASTOUT%
IF %ERRORLEVEL% GEQ 1 (
    ECHO ERRORLEVEL: %ERRORLEVEL%
    TYPE L.stdout.tmp
    GOTO :ERROR
)
COPY /Y L.stdout.tmp %PROGOUT% >NUL
%L% %IN%.L >>%PROGOUT%
IF %ERRORLEVEL% GEQ 1 (
    ECHO ERRORLEVEL: %ERRORLEVEL%
    TYPE %PROGOUT%
    GOTO :ERROR
)
TYPE %PROGOUT%
GOTO :DONE


:QASTONLY
COPY /Y L.stdout.tmp %QASTOUT% >NUL
ECHO $ %L% --target=ast %IN%.L
%L% --target=ast %IN%.L >>%QASTOUT%
IF %ERRORLEVEL% GEQ 1 (
    ECHO ERRORLEVEL: %ERRORLEVEL%
    GOTO :ERROR
)
TYPE %QASTOUT%
GOTO :DONE


:DONE
DEL L.stdout.tmp
EXIT /B 0


:ERROR
DEL L.stdout.tmp
EXIT /B 1
