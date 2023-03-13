#! /bin/bash

echo "method m() { assert 1+1 == 2; }" > a.dfy
echo "method m() { assert 1+1 == 3; }" > b.dfy
echo 'method Main() { print (42,131), "\n"; }' > c.dfy

DIR="$(dirname ${BASH_SOURCE[0]})"
echo Should succeed
$DIR/dafny /compile:0 a.dfy
echo Should fail
$DIR/dafny /compile:0 -useBaseNameForFileName b.dfy
echo Compiling on C#
$DIR/dafny /compile:3 /compileVerbose:0 /compileTarget:cs c.dfy
echo Compiling to Javascript
$DIR/dafny /compile:3 /compileVerbose:0 /compileTarget:js c.dfy
echo Compiling to Java
$DIR/dafny /compile:3 /compileVerbose:0 /compileTarget:java c.dfy
echo Compiling to Go
$DIR/dafny /compile:3 /compileVerbose:0 /compileTarget:go c.dfy
echo Compiling to Python
$DIR/dafny /compile:3 /compileVerbose:0 /compileTarget:py c.dfy
rm -rf a.dfy b.dfy c.dfy c-go c-java c-py c.jar c
