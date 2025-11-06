#!/bin/bash

echo "method m() { assert 1+1 == 2; }" > a.dfy
echo "method m() { assert 1+1 == 3; }" > b.dfy
echo 'method Main() { print (42,131), "\n"; }' > c.dfy

tmp=quicktest.tmp
tmpx=quicktest.tmpx
error_count=0

DAFNY=/usr/local/bin/dafny

# Test 1
echo "" > $tmp
echo "Dafny program verifier finished with 0 verified, 0 errors" >> $tmp
echo "(42, 131)" >> $tmp

echo -n "[Test 1/2] Running with Java ..."
if $DAFNY run -t:java c.dfy | diff - $tmp; then
    echo -e "\r[Test 1/2] Running with Java [\033[32m✓\033[0m]"
else
    echo -e "\r[Test 1/2] Running with Java [\033[31m✗\033[0m]"
    ((error_count++))
fi

rm -rf c-java c.jar

# Test 2
echo "" > $tmp
echo "Dafny program verifier finished with 0 verified, 0 errors" >> $tmp
echo "(42, 131)" > $tmpx

echo -n "[Test 2/2] Building with Java ..."
if $DAFNY build -t:java c.dfy | diff - $tmp && java -jar c.jar | diff - $tmpx; then
    echo -e "\r[Test 2/2] Building with Java [\033[32m✓\033[0m]"
else
    echo -e "\r[Test 2/2] Building with Java [\033[31m✗\033[0m]"
    ((error_count++))
fi

if [ $error_count -eq 0 ]; then
    echo "--- test_java script completed ---"
else
    echo "--- test_java script completed with $error_count error(s) ---"
fi

rm -rf a.dfy b.dfy c.dfy c-java c.jar
rm $tmp $tmpx

exit $error_count