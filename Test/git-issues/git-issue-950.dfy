// RUN: %baredafny verify %args "%s" "%s" > "%t"
// RUN: %baredafny verify %args "%s" %S/git-issue-950.dfy >> "%t"
// RUN: %baredafny verify %args "%s" %S/../git-issues/git-issue-950.dfy >> "%t"
// RUN: %diff "%s.expect" "%t"

module M {

  const x: int := 5
  method m() {
    assert x == 5;
  }
}
