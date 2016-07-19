@echo off
"c:/boogie/Binaries/Dafny.exe" -nologo -compile:0 /print:xxx.bpl -timeLimit:60 %* > c:\tmp\jen-doo.out
