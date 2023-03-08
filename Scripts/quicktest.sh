#! /bin/bash

echo "method m() { assert 1+1 == 2; }" > a.dfy
echo "method m() { assert 1+1 == 3; }" > b.dfy
echo "method Main() { print (42,131), '\n'; }" > c.dfy

DIR="$(dirname ${BASH_SOURCE[0]})"
if [ -n "$1" ]; then
  DAFNY=$1
else
  DAFNY=$DIR/dafny
fi

echo Should succeed
$DAFNY verify a.dfy
echo Should fail
$DAFNY verify --use-basename-for-filename  b.dfy
echo Compiling on C#
$DAFNY run -t:cs c.dfy
echo Compiling to Javascript
$DAFNY run -t:js c.dfy
echo Compiling to Java
$DAFNY run -t:java c.dfy
echo Compiling to Go
$DAFNY run -t:go c.dfy
echo Compiling to Python
$DAFNY run -t:py c.dfy
echo Building on C#
$DAFNY build -t:cs c.dfy
dotnet c.dll
echo Building to Javascript
$DAFNY build -t:js c.dfy
node c.js
echo Building to Java
$DAFNY build -t:java c.dfy
java -jar c.jar
echo Building to Go
$DAFNY build -t:go c.dfy
(cd c-go; GO111MODULE=auto GOPATH=`pwd` go run src/c.go)
echo Building to Python
$DAFNY build -t:py c.dfy
python c-py/c.py

rm -rf a.dfy b.dfy c.dfy c-go c-java c-py c.jar c c.dll c.exe
