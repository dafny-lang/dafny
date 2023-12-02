// RUN: %exits-with 2 %baredafny resolve --show-snippets:false --use-basename-for-filename "%s" > "%t"
// RUN: %exits-with 2 %baredafny resolve --show-snippets:false --use-basename-for-filename --library:"%S/src/A.dfy" "%s" >> "%t"
// RUN: %baredafny resolve --show-snippets:false --use-basename-for-filename --library:"%S/src/A.dfy,%S/src/sub/B.dfy" "%s" >> "%t"
// RUN: %baredafny resolve --show-snippets:false --use-basename-for-filename --library:"%S/src/A.dfy , %S/src/sub/B.dfy" "%s" >> "%t"
// RUN: %baredafny resolve --show-snippets:false --use-basename-for-filename --library:"%S/src" "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

module M {
  import A
}
