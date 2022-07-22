// dafny should emit exit value 1
// RUN: %dafny_0 /compile:3 x.cs > "%t"
// RUN: %diff "%s.expect" "%t"
