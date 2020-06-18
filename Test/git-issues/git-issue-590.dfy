// RUN: %dafny /compile:3 x.cs > "%t"
// RUN: %diff "%s.expect" "%t"
// XFAIL: *
