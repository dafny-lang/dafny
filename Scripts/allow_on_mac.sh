#! /bin/bash

cd "$( dirname "${BASH_SOURCE[0]}" )" || exit 1
xattr -d com.apple.quarantine ./*.dylib dafny DafnyServer ./*.dll z3/bin/z3*
