// RUN: %baredafny build %args "%s"                                                > "%t"
// RUN: %baredafny build %args "%s" --verbose=true %S/"git-issue-289b.dfy" >> "%t"
// RUN: %baredafny build %args                             %S/"git-issue-289b.dfy" >> "%t"
// RUN: %diff "%s.expect" "%t"

include "git-issue-289b.dfy"
