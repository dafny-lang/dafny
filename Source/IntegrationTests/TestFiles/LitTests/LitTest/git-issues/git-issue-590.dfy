// dafny should emit exit value 1
// RUN: ! %run x.cs > "%t"
// RUN: %diff "%s.expect" "%t"
