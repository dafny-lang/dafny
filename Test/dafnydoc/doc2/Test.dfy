// RUN: rm -rf "%S"/docs "%S"/docs2
// RUN: %baredafny doc --use-basename-for-filename "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// RUN: %diff "%S"/docs/index.html "%S"/docs-expected/index.html
// RUN: %diff "%S"/docs/nameindex.html "%S"/docs-expected/nameindex.html
// RUN: %diff "%S"/docs/_.html "%S"/docs-expected/_.html
// RUN: %diff "%S"/docs/Test.html "%S"/docs-expected/Test.html
// RUN: %baredafny doc --use-basename-for-filename --output="%S"/docs2 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// RUN: %diff "%S"/docs2/index.html "%S"/docs-expected/index.html

module Test {}
