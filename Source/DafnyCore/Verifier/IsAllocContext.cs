using Microsoft.Dafny;

public class IsAllocContext {
  private DafnyOptions options;
  internal bool allVarsGhost;

  internal IsAllocContext(DafnyOptions options, bool allVarsGhost) {
    this.options = options;
    this.allVarsGhost = allVarsGhost;
  }

  internal IsAllocType Var(bool isGhost) {
    return BoogieGenerator.ISALLOC;
  }

  internal IsAllocType Var(LocalVariable local) {
    return Var(allVarsGhost || local.IsGhost);
  }

  internal IsAllocType Var(NonglobalVariable var) {
    return Var(allVarsGhost || var.IsGhost);
  }

  internal IsAllocType Var(bool ghostStmt, LocalVariable var) {
    return Var(allVarsGhost || ghostStmt || var.IsGhost);
  }

  internal IsAllocType Var(bool ghostStmt, NonglobalVariable var) {
    return Var(allVarsGhost || ghostStmt || var.IsGhost);
  }
}