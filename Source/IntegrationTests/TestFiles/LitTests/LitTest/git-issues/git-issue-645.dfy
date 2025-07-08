// dafny should emit exit value 1
// RUN: ! %dafny /xyz /useBasenameForFilename  > "%t"
// RUN: %diff "%s.expect" "%t"
// UNSUPPORTED: windows
