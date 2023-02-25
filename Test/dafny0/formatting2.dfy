// RUN: %exits-with 2 %baredafny format --use-basename-for-filename --print "unexisting.dfy" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
}
