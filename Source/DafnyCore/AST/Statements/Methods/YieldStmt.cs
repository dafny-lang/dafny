using System.Collections.Generic;

namespace Microsoft.Dafny;

public class YieldStmt : ProduceStmt, ICloneable<YieldStmt>, ICanFormat {
  public YieldStmt Clone(Cloner cloner) {
    return new YieldStmt(cloner, this);
  }

  public YieldStmt(Cloner cloner, YieldStmt original) : base(cloner, original) {
  }

  public YieldStmt(IOrigin rangeOrigin, List<AssignmentRhs> rhss)
    : base(rangeOrigin, rhss, null) {
  }

  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    return formatter.SetIndentAssertLikeStatement(this, indentBefore);
  }
}