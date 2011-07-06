@echo off
echo ---------- Starting ------------ < nul >> c:\tmp\doo.out
time < nul >> c:\tmp\doo.out
echo. < nul >> c:\tmp\doo.out

"c:\boogie\Binaries\Dafny.exe" -nologo stdin.dfy -compile:0 -timeLimit:10 %* 2>> c:\tmp\doo.out

time < nul >> c:\tmp\doo.out
echo. < nul >> c:\tmp\doo.out
echo ---------- Done ------------ < nul >> c:\tmp\doo.out
