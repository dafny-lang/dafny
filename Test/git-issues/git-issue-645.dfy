// dafny should emit exit value 1
// RUN: %dafny /xyz    > "%t" || true
// RUN: %diff "%s.expect" "%t"
// UNSUPPORTED: windows
