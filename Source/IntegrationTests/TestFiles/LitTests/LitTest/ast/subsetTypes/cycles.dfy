// RUN: ! %verify %s &> "%t"
// RUN: %diff "%s.expect" "%t"

datatype Stmt =
  | Skip
  | Block(stmts: seq<Stmt>)
  | If(b: bool, thn: BlockStmt, els: BlockStmt)

type BlockStmt = s: Stmt | s.Block? witness Block([])
//   ^^^^^^^^^ error: recursive constraint dependency involving a subset type: BlockStmt -> Stmt -> BlockStmt