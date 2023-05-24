// dafny should emit exit value 1
// RUN: ! %dafny /xyz /useBasenameForFilename  2> "%t"
// RUN: %diff "%s.expect" "%t"
// UNSUPPORTED: windows
