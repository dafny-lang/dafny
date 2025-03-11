#nullable enable
using System.Linq;

namespace Microsoft.Dafny;

public abstract class NodeWithOrigin : Node {
  private IOrigin origin;

  protected NodeWithOrigin(Cloner cloner, NodeWithOrigin original)
    : this(cloner.Origin(original.Origin)) {
  }

  [SyntaxConstructor]
  protected NodeWithOrigin(IOrigin? origin) {
    this.origin = origin ?? Token.NoToken;
  }

  public void SetOrigin(IOrigin newOrigin) {
    origin = newOrigin;
    entireRange = null;
  }

  public override IOrigin Origin => origin;


  private TokenRange? entireRange;

  public override TokenRange EntireRange {
    get {
      if (entireRange == null) {
        if (Origin.EntireRange == null) {
          var start = ReportingRange.StartToken;
          var end = ReportingRange.EndToken;

          // Since the children are not ordered, we have to traverse them all
          foreach (var child in PreResolveChildren) {
            if (child.Origin.Filepath != origin.Filepath || child is Expression { IsImplicit: true } ||
                child is DefaultValueExpression) {
              // Ignore any auto-generated expressions.
              continue;
            }

            UpdateStartEndToken(child.StartToken);
            UpdateStartEndToken(child.EndToken);
          }

          entireRange = new TokenRange(start, end);

          void UpdateStartEndToken(Token newToken) {
            if (newToken.Filepath != origin.Filepath) {
              return;
            }

            if (newToken.pos < start.pos) {
              start = newToken;
            }

            if (newToken.pos + newToken.val.Length > end.pos + end.val.Length) {
              end = newToken;
            }
          }
        } else {
          entireRange = origin.EntireRange!;
        }
      }

      return entireRange;


    }
  }
}