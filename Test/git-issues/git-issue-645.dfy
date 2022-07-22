// dafny should emit exit value 1
// RUN: %dafny_0 /xyz    > "%t"
// RUN: %diff "%s.expect" "%t"
// UNSUPPORTED: windows
