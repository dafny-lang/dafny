#!/usr/bin/env bash

# find the source directory for this script even if it's been symlinked [issue #185]
# from https://stackoverflow.com/questions/59895/
SOURCE="${BASH_SOURCE[0]}"
while [ -h "$SOURCE" ]; do
    DIR="$( cd -P "$( dirname "$SOURCE" )" && pwd )"
    SOURCE="$(readlink "$SOURCE")"
    [[ $SOURCE != /* ]] && SOURCE="$DIR/$SOURCE"
done
DAFNY_ROOT="$( cd -P "$( dirname $( dirname "$SOURCE" ))" && pwd )"

cd $DAFNY_ROOT
pre-commit install
npm install bignumber.js 
cd $DAFNY_ROOT/Binaries
ln -s /opt/z3/z3-4.8.5-x64-ubuntu-16.04/ z3
