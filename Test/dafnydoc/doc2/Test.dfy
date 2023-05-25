// RUN: rm -rf "%S"/docs "%S"/docs2
// RUN: %baredafny doc --use-basename-for-filename "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// RUN: %diff "%S"/docs/index.html "%S"/docs-expected/index.html
// RUN: %diff "%S"/docs/__95.html "%S"/docs-expected/__95.html
// RUN: %diff "%S"/docs/Test_13716.html "%S"/docs-expected/Test_13716.html
// RUN: %baredafny doc --use-basename-for-filename --output="%S"/docs2 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// RUN: %diff "%S"/docs2/index.html "%S"/docs-expected/index.html

module Test {}
