using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class WildcardExpr : Expression, ICloneable<WildcardExpr> {  // a WildcardExpr can occur only in reads clauses and a loop's decreases clauses (with different meanings)

  public WildcardExpr(Cloner cloner, WildcardExpr original) : base(cloner, original) {
  }

  public WildcardExpr(IOrigin tok)
    : base(tok) {
    Contract.Requires(tok != null);
  }

  public WildcardExpr Clone(Cloner cloner) {
    return new WildcardExpr(cloner, this);
  }
}