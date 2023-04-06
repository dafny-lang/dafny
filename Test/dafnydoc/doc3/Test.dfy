// RUN: %exits-with 2 %baredafny doc --use-basename-for-filename "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Test {}
