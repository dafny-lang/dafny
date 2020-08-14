// RUN: %dafny /compile:0  "%s" > "%t"
// RUN: %dafny /compile:0 /z3exe:"%S"/../../Binaries/z3/bin/z3 "%s" >> "%t"
// RUN: cp -r "%S"/../../Binaries/z3/bin "%S"/../../Binaries/z3/binx
// RUN: %dafny /compile:0 /z3exe:"%S"/../../Binaries/z3/binx/z3 "%s" >> "%t"
// RUN: rm -rf "%S"/../../Binaries/z3/binx
// RUN: %diff "%s.expect" "%t"

method m() {
  assert 1 + 1 == 2;
}
