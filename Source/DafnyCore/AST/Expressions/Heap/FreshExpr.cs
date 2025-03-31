using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class FreshExpr : UnaryOpExpr, ICloneable<FreshExpr> {
  public string/*?*/ At;
  [FilledInDuringResolution] public Label/*?*/ AtLabel;  // after that, At==null iff AtLabel==null

  public FreshExpr(IOrigin origin, Expression e, string at = null)
    : base(origin, Opcode.Fresh, e) {
    Contract.Requires(origin != null);
    Contract.Requires(e != null);
    this.At = at;
  }

  public FreshExpr(Cloner cloner, FreshExpr original) : base(cloner, original) {
    At = original.At;
    if (cloner.CloneResolvedFields) {
      AtLabel = original.AtLabel;
    }
  }

  public new FreshExpr Clone(Cloner cloner) { return new FreshExpr(cloner, this); }
}