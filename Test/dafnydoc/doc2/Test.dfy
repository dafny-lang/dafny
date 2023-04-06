// RUN: rm -rf docs docs2
// RUN: %baredafny doc --use-basename-for-filename "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// RUN: %diff docs/index.html docs-expected/index.html
// RUN: %diff docs/nameindex.html docs-expected/nameindex.html
// RUN: %diff docs/_.html docs-expected/_.html
// RUN: %diff docs/Test.html docs-expected/Test.html
// RUN: %baredafny doc --use-basename-for-filename --output=./docs2 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// RUN: %diff docs2/index.html docs-expected/index.html

module Test {}
