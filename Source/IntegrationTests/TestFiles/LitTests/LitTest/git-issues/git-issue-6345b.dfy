// RUN: %exits-with 2 %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// MatchFlattener is not only run on error-free ASTs: ModuleResolver.MakeAbstractSignature calls
// it unconditionally, unlike LiteralModuleDecl.Resolve, which skips the rewriters when the error
// count rose. Bounds discovery and type inference are error-gated, so on an erroneous module the
// AST reaching MatchFlattener still has null ForallStmt.Bounds and null Expression.Type, and
// flattening it crashed instead of reporting the errors below.
//
// The `Bad` error is what keeps bounds discovery and type inference from running; the forall
// inside the match is what gets cloned with a null Bounds list. Two distinct crashes reach this
// input, so the null-conditional in the ForallStmt clone constructor is not enough on its own:
// gating the flattener is what lets the errors be reported. The duplicated error is pre-existing
// and unrelated -- an abstract import of an erroneous module reports it once per module.

module Template {
  datatype D = X | Y
  function Bad(): int { true }
  function F(d: D): int {
    match d
    case X => (forall i: int | 0 <= i < 5 ensures true { } 3)
    case Y => 4
  }
}

abstract module Client { import T : Template }
