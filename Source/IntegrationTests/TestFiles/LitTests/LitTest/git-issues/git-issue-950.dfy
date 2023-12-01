// RUN: %verify "%s" "%s" > "%t"
// RUN: %verify "%s" %S/git-issue-950.dfy >> "%t"
// RUN: %verify "%s" %S/../git-issues/git-issue-950.dfy >> "%t"
// RUN: %diff "%s.expect" "%t"

module M {

  const x: int := 5
  method m() {
    assert x == 5;
  }
}
