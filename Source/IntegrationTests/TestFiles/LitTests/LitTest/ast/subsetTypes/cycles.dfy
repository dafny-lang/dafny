// RUN: ! %verify --type-system-refresh --general-traits=datatype %s &> "%t"
// RUN: %diff "%s.expect" "%t"

datatype Stmt =
  | Skip
  | Block(stmts: seq<Stmt>)
  | If(b: bool, thn: BlockStmt, els: BlockStmt)

type BlockStmt = s: Stmt | s.Block? witness Block([])
