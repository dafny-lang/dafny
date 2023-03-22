#! /bin/bash

echo "method m() { assert 1+1 == 2; }" > a.dfy
echo "method m() { assert 1+1 == 3; }" > b.dfy
echo 'method Main() { print (42,131), "\n"; }' > c.dfy

tmp=quicktest.tmp
tmpx=quicktest.tmpx

DIR="$(dirname ${BASH_SOURCE[0]})"
if [ -n "$1" ]; then
  DAFNY=$1
else
  DAFNY=$DIR/dafny
fi
##echo "Using:" $DAFNY

echo "" > $tmp
echo "Dafny program verifier finished with 1 verified, 0 errors" >> $tmp

echo Should succeed
$DAFNY verify a.dfy | diff - $tmp || exit 1

echo "b.dfy(1,24): Error: assertion might not hold" > $tmp
echo "" >> $tmp
echo "Dafny program verifier finished with 0 verified, 1 error" >> $tmp

echo Should fail
$DAFNY verify --use-basename-for-filename b.dfy | diff - $tmp

echo "" > $tmp
echo "Dafny program verifier finished with 0 verified, 0 errors" >> $tmp
echo "(42, 131)" >> $tmp

echo Running with C#
$DAFNY run -t:cs c.dfy | diff - $tmp || exit 1
echo Running with Javascript
$DAFNY run -t:js c.dfy | diff - $tmp || exit 1
echo Running with Java
$DAFNY run -t:java c.dfy | diff - $tmp || exit 1
echo Running with Go
$DAFNY run -t:go c.dfy | diff - $tmp || exit 1
echo Running with Python
$DAFNY run -t:py c.dfy | diff - $tmp || exit 1

rm -rf c-go c-java c-py c.jar c c.dll c.exe c.js c.runtimeconfig.json
echo "" > $tmp
echo "Dafny program verifier finished with 0 verified, 0 errors" >> $tmp
echo "(42, 131)" > $tmpx

echo Building with C#
$DAFNY build -t:cs c.dfy | diff - $tmp || exit 1
dotnet c.dll | diff - $tmpx || exit 1
echo Building with Javascript
$DAFNY build -t:js c.dfy | diff - $tmp || exit 1
node c.js | diff - $tmpx || exit 1
echo Building with Java
$DAFNY build -t:java c.dfy | diff - $tmp || exit 1
java -jar c.jar | diff - $tmpx || exit 1
echo Building with Go
$DAFNY build -t:go c.dfy | diff - $tmp || exit 1
./c | diff - $tmpx || exit 1
(cd c-go; GO111MODULE=auto GOPATH=`pwd` go run src/c.go) | diff - $tmpx || exit 1
echo Building with Python
$DAFNY build -t:py c.dfy | diff - $tmp || exit 1
python c-py/c.py | diff - $tmpx || exit 1

echo Quicktest script succeeded

rm -rf a.dfy b.dfy c.dfy c-go c-java c-py c.jar c c.dll c.exe c.js c.runtimeconfig.json
rm $tmp $tmpx
