// RUN: %dafny /useBaseNameForFileName /compile:0 %S/git-issue-1838.dfy > "%t"
// RUN: %diff "%s.expect" "%t"

module A.B {
  type u64 = x | 0 <= x <= 0xffff_ffff_ffff_ffff
}
