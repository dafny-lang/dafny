using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class ReturnStmt : ProduceStmt, ICloneable<ReturnStmt> {
  public bool ReverifyPost;  // set during pre-resolution refinement transformation

  public ReturnStmt Clone(Cloner cloner) {
    return new ReturnStmt(cloner, this);
  }

  public ReturnStmt(Cloner cloner, ReturnStmt original) : base(cloner, original) {
    ReverifyPost = original.ReverifyPost;
  }

  public ReturnStmt(IOrigin rangeOrigin, List<AssignmentRhs> rhss, Attributes attributes = null)
    : base(rangeOrigin, rhss, attributes) {
    Contract.Requires(rangeOrigin != null);
  }
}