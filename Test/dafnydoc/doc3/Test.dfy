// RUN: chmod ugo-x docs
// RUN: %exits-with 2 %baredafny doc --use-basename-for-filename "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// UNSUPPORTED: windows

module Test {}
