// RUN: %dafny /compile:0 "%s" "%s" > "%t"
// RUN: %dafny /compile:0 "%s" %S/git-issue-950.dfy >> "%t"
// RUN: %dafny /compile:0 "%s" %S/../git-issues/git-issue-950.dfy >> "%t"
// RUN: %diff "%s.expect" "%t"

module M {

  const x: int := 5
  method m() {
    assert x == 5;
  }
}
