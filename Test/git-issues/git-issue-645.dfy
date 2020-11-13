// dafny should emit exit value 1
// RUN: %dafny /xyz    > "%t" || echo ERROR EXIT >> "%t"
// RUN: %diff "%s.expect" "%t"
