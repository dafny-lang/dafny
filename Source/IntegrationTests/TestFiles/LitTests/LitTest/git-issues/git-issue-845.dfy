// RUN: %verify %S/git-issue-845.dfy --allow-warnings > "%t"
// RUN: %diff "%s.expect" "%t"

/* blah blah /* blah */
method foo() returns (r:bool) { assert true == false; }


