// RUN: %build --skip-included-files "%s"                                                > "%t"
// RUN: %build --skip-included-files "%s" --verbose=true %S/"git-issue-289b.dfy" >> "%t"
// RUN: %build --skip-included-files                             %S/"git-issue-289b.dfy" >> "%t"
// RUN: %diff "%s.expect" "%t"

include "git-issue-289b.dfy"
