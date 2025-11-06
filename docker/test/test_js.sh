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

echo -n "[Test 1/2] Running with Javascript ..."
if $DAFNY run -t:js c.dfy | diff - $tmp; then
    echo -e "\r[Test 1/2] Running with Javascript [\033[32m✓\033[0m]"
else
    echo -e "\r[Test 1/2] Running with Javascript [\033[31m✗\033[0m]"
    ((error_count++))
fi

rm -rf c.js

# Test 2
echo "" > $tmp
echo "Dafny program verifier finished with 0 verified, 0 errors" >> $tmp
echo "(42, 131)" > $tmpx

echo -n "[Test 2/2] Building with Javascript ..."
if $DAFNY build -t:js c.dfy | diff - $tmp && node c.js | diff - $tmpx; then
    echo -e "\r[Test 2/2] Building with Javascript [\033[32m✓\033[0m]"
else
    echo -e "\r[Test 2/2] Building with Javascript [\033[31m✗\033[0m]"
    ((error_count++))
fi

if [ $error_count -eq 0 ]; then
    echo "--- test_js script completed ---"
else
    echo "--- test_js script completed with $error_count error(s) ---"
fi

rm -rf a.dfy b.dfy c.dfy c.js
rm $tmp $tmpx

exit $error_count