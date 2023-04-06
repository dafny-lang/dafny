// RUN: %baredafny doc --use-basename-for-filename --verbose "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Test {}
