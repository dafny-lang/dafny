// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This case used to cause duplicate Boogie variable declarations
// because MatchFlattner was not cloning NestedMatchCaseStmts as it
// created multiple copies for disjunctive patterns.

method mmm() returns (i: int) {
  match "abc"
    case "def"|"ghi" => { var st := 0; return st; }
    case _ => { return 1; }
}

// Whereas this case produced the same symptom but for a different reason:
// incorrect cloning of CasePatterns that resulted in not cloning LocalVariable
// declarations.  

datatype Choice = A | B | C

method Foo(x: Choice) returns (r: bool) {
  match x {
    case A => return true;
    case _ => 
      var (x, y) := (42, 43);
      return false;
  }
}