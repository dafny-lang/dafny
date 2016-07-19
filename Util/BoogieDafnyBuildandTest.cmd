@echo off
pushd ..\test
goto Cleanandbuild

:Cleanandbuild
cls
@echo on
devenv ..\Source\Boogie.sln /Clean
@echo off
if errorlevel 1 goto fail
@echo on
devenv ..\source\Boogie.sln /Build
@echo off
if errorlevel 1 goto fail
@echo on
devenv ..\Source\Dafny.sln /Clean
@echo off
if errorlevel 1 goto fail
@echo on
devenv ..\Source\Dafny.sln /Build
@echo off
if errorlevel 1 goto fail
goto reg

:Reg
cls
call runtestall
goto end

:fail
echo Some part of the rebuild failed.
goto end

:end
popd