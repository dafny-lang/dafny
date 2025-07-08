// RUN: %exits-with 2 %resolve --allow-warnings "%s" > "%t"
// RUN: %exits-with 2 %resolve --allow-warnings --library:"%S/src/A.dfy" "%s" >> "%t"
// RUN: %resolve --allow-warnings --library:"%S/src/A.dfy,%S/src/sub/B.dfy" "%s" >> "%t"
// RUN: %resolve --allow-warnings --library:"%S/src/A.dfy , %S/src/sub/B.dfy" "%s" >> "%t"
// RUN: %resolve --allow-warnings --library:"%S/src" "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

module M {
  import A
}
