#! /bin/bash

cd $( dirname $SOURCE )
xattr -d com.apple.quarantine *.dylib dafny DafnyServer *.dll z3/bin/z3
