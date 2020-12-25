// RUN: %dafny /compile:0  "%s" > "%t"
// RUN: %dafny /compile:0 /z3exe:"%S"/../../Binaries/z3/bin/z3 "%s" >> "%t"
// RUN: cp -r "%S"/../../Binaries/z3/bin Output/binx
// RUN: %dafny /compile:0 /z3exe:Output/binx/z3 "%s" >> "%t"
// RUN: rm -rf Output/binx
// RUN: %diff "%s.expect" "%t"
// UNSUPPORTED: windows
method m() {
  assert 1 + 1 == 2;
}
