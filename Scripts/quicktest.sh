#! /bin/bash

echo "method m() { assert 1+1 == 2; }" > a.dfy
echo "method m() { assert 1+1 == 3; }" > b.dfy
echo 'method Main() { print (42,131), "\n"; }' > c.dfy

DIR="$(dirname ${BASH_SOURCE[0]})"
if [ -n "$1" ]; then
  DAFNY=$1
else
  DAFNY=$DIR/dafny
fi
echo "Using:" $DAFNY

echo Should succeed
$DAFNY verify a.dfy
echo Should fail
$DAFNY verify --use-basename-for-filename  b.dfy
echo Compiling on C#
$DAFNY run -t:cs c.dfy
echo Compiling on Javascript
$DAFNY run -t:js c.dfy
echo Compiling on Java
$DAFNY run -t:java c.dfy
echo Compiling on Go
$DAFNY run -t:go c.dfy
echo Compiling on Python
$DAFNY run -t:py c.dfy
echo Building on C#
rm -rf c-go c-java c-py c.jar c c.dll c.exe c.js c.runtimeconfig.json
$DAFNY build -t:cs c.dfy
dotnet c.dll
echo Building on Javascript
$DAFNY build -t:js c.dfy
node c.js
echo Building on Java
$DAFNY build -t:java c.dfy
java -jar c.jar
echo Building on Go
$DAFNY build -t:go c.dfy
./c
(cd c-go; GO111MODULE=auto GOPATH=`pwd` go run src/c.go)
echo Building on Python
$DAFNY build -t:py c.dfy
python c-py/c.py

rm -rf a.dfy b.dfy c.dfy c-go c-java c-py c.jar c c.dll c.exe c.js c.runtimeconfig.json
