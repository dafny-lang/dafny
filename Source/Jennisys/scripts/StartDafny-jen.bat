@echo off
"c:/boogie/Binaries/Dafny.exe" -compile:0 /print:xxx.bpl -timeLimit:60 %* > c:\tmp\jen-doo.out
