// RUN: %build -t:lib "%s" --output "%S/Output/git-issue-6436.doo" > "%t"
// RUN: %verify "%S/Output/git-issue-6436.doo" >> "%t"
// RUN: %diff "%s.expect" "%t"

// Regression test: set comprehension as a non-last function argument lost its
// parentheses when serialized to a doo file, causing a parse error on reload.

predicate g(x: set<nat>, y: nat)
predicate f(x: set<nat>, y: nat) { g((set i <- x), y) }

// Also test first-class function application (ApplyExpr):
ghost predicate h(p: (set<nat>, nat) -> bool, x: set<nat>, y: nat) {
  p((set i <- x), y)
}
