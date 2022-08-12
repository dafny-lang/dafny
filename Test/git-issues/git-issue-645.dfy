// dafny should emit exit value 1
// RUN: %dafny_0 /xyz    > "%t" || true
// RUN: %diff "%s.expect" "%t"
// UNSUPPORTED: windows
