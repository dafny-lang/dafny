// RUN: %exits-with 1 %baredafny format --use-basename-for-filename --print "%S/unexisting.dfy" > "%t.raw"
// RUN: %sed 's#%S##g' "%t.raw" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
}
