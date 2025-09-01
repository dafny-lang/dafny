// RUN: ! %verify --type-system-refresh --general-traits=datatype %s &> "%t"
// RUN: %diff "%s.expect" "%t"

datatype Stmt =
  | Skip
  | Block(stmts: seq<Stmt>)
  | If(b: bool, thn: BlockStmt, els: BlockStmt)

type BlockStmt = s: Stmt | s.Block? witness Block([])

trait SelfConstraintDep<T extends SelfConstraintDep<T>> {}
trait SelfConstraintDep2<T extends SelfConstraintDep2<T>> extends object {}

datatype D extends SelfConstraintDep<D> = D {}
class C extends SelfConstraintDep2<C> {}