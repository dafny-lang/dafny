// RUN: %baredafny verify %args "%s"                                                > "%t"
// RUN: %baredafny verify %args "%s" %S/"git-issue-289b.dfy" >> "%t"
// RUN: %baredafny verify %args      %S/"git-issue-289b.dfy" >> "%t"
// RUN: %diff "%s.expect" "%t"

include "git-issue-289b.dfy"
