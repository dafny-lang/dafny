using System;
using System.Collections.Generic;

namespace Microsoft.Dafny;

class ClonerButIVariablesAreKeptOnce : ClonerKeepParensExpressions {
  private readonly HashSet<IVariable> alreadyCloned = [];

  private VT CloneIVariableHelper<VT>(VT local, Func<VT, VT> returnMethod) where VT : IVariable {
    if (!alreadyCloned.Contains(local)) {
      alreadyCloned.Add(local);
      return local;
    }

    return returnMethod(local);
  }

  public override LocalVariable CloneLocalVariable(LocalVariable local, bool isReference) {
    return CloneIVariableHelper(local, v => base.CloneLocalVariable(v, isReference));
  }

  public override Formal CloneFormal(Formal local, bool isReference) {
    return CloneIVariableHelper(local, f => base.CloneFormal(f, isReference));
  }
  public override BoundVar CloneBoundVar(BoundVar local, bool isReference) {
    return CloneIVariableHelper(local, v => base.CloneBoundVar(v, isReference));
  }
}
