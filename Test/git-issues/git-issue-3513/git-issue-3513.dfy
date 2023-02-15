// RUN: %exits-with 2 %baredafny resolve --use-basename-for-filename "%s" > "%t"
// RUN: %exits-with 2 %baredafny resolve --use-basename-for-filename --library:src/A.dfy "%s" >> "%t"
// RUN: %baredafny resolve --use-basename-for-filename --library:src "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

module M {
  import A
}
