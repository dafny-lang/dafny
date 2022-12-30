using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class ReturnStmt : ProduceStmt {
  public bool ReverifyPost;  // set during pre-resolution refinement transformation
  public ReturnStmt(IToken tok, IToken endTok, List<AssignmentRhs> rhss)
    : base(tok, endTok, rhss) {
    Contract.Requires(tok != null);
    Contract.Requires(endTok != null);
  }
}