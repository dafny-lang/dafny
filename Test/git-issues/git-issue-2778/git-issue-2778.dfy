// RUN: %baredafny resolve --use-basename-for-filename "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class {:handle} A {}

method {:dllimport "x"} m() {}
