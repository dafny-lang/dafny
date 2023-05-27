// RUN: rm -rf "%S"/docs "%S"/docs2
// RUN: %baredafny doc --use-basename-for-filename "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// RUN: %baredafny doc --use-basename-for-filename --output="%S"/docs2 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Test {}
