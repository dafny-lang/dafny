// dafny should emit exit value 1
// RUN: %dafny_0 /compile:3 x.cs > "%t" || true
// RUN: %diff "%s.expect" "%t"
