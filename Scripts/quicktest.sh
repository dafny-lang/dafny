#! /bin/bash

echo "method m() { assert 1+1 == 2; }" > a.dfy
echo "method m() { assert 1+1 == 3; }" > b.dfy
echo "method Main() { print (42,131), '\n'; }" > c.dfy

DIR="$(dirname ${BASH_SOURCE[0]})"
echo Should succeed
$DIR/dafny verify a.dfy
echo Should fail
$DIR/dafny verify --use-basename-for-filename  b.dfy
echo Compiling on C#
$DIR/dafny run -t:cs c.dfy
echo Compiling to Javascript
$DIR/dafny run -t:js c.dfy
echo Compiling to Java
$DIR/dafny run -t:java c.dfy
echo Compiling to Go
$DIR/dafny run -t:go c.dfy
echo Compiling to Python
$DIR/dafny run -t:py c.dfy
echo Building on C#
$DIR/dafny build -t:cs c.dfy
dotnet c.dll
echo Building to Javascript
$DIR/dafny build -t:js c.dfy
node c.js
echo Building to Java
$DIR/dafny build -t:java c.dfy
java -jar c.jar
echo Building to Go
$DIR/dafny build -t:go c.dfy
(cd c-go; GO111MODULE=auto GOPATH=`pwd` go run src/c.go)
echo Building to Python
$DIR/dafny build -t:py c.dfy
python c-py/c.py

#rm -rf a.dfy b.dfy c.dfy c-go c-java c-py c.jar c
