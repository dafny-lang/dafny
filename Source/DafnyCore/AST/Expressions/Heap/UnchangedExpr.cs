using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class UnchangedExpr : Expression, ICloneable<UnchangedExpr>, ICanFormat {
  public readonly List<FrameExpression> Frame;
  public readonly string/*?*/ At;
  [FilledInDuringResolution] public Label/*?*/ AtLabel;  // after that, At==null iff AtLabel==null
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Frame != null);
  }

  public UnchangedExpr Clone(Cloner cloner) {
    return new UnchangedExpr(cloner, this);
  }

  public UnchangedExpr(Cloner cloner, UnchangedExpr original) : base(cloner, original) {
    Frame = original.Frame.ConvertAll(cloner.CloneFrameExpr);
    At = original.At;
    if (cloner.CloneResolvedFields) {
      AtLabel = original.AtLabel;
    }
  }

  public UnchangedExpr(IOrigin tok, List<FrameExpression> frame, string/*?*/ at)
    : base(tok) {
    Contract.Requires(tok != null);
    Contract.Requires(frame != null);
    this.Frame = frame;
    this.At = at;
  }

  public override IEnumerable<Expression> SubExpressions {
    get {
      foreach (var fe in Frame) {
        yield return fe.E;
      }
    }
  }

  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    return formatter.SetIndentParensExpression(indentBefore, OwnedTokens);
  }
}