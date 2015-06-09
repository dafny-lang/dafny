@REM runTests.bat -f "/dprelude PRELUDE_FILE" -r REPORT_NAME INPUT_FILES
C:/Python34/python.exe runTests.py --compiler "c:/MSR/dafny/Binaries/Dafny.exe /useBaseNameForFileName /compile:1 /nologo" --difftool "C:\Program Files (x86)\Meld\Meld.exe" -j4 %*
