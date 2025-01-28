#nullable enable
using Microsoft.Boogie;

namespace Microsoft.Dafny;

public abstract class NodeWithComputedRange : Node {
  // Contains tokens that did not make it in the AST but are part of the expression,
  // Enables ranges to be correct.
  // TODO: Re-add format tokens where needed until we put all the formatting to replace the tok of every expression
  internal Token[]? FormatTokens = null;

  private IOrigin origin;

  [ParseConstructor]
  protected NodeWithComputedRange(IOrigin? origin = null) {
    this.origin = origin ?? Token.NoToken;
  }

  protected NodeWithComputedRange(Cloner cloner, NodeWithComputedRange original) {
    origin = cloner.Origin(original.Origin);
  }

  public void SetOrigin(IOrigin newOrigin) {
    origin = newOrigin;
  }

  public override IOrigin Origin {
    get {
      if (origin is Token tokenOrigin) {

        var startTok = origin.StartToken;
        var endTok = origin.EndToken;

        void UpdateStartEndToken(Token token1) {
          if (token1.Filepath != origin.Filepath) {
            return;
          }

          if (token1.pos < startTok.pos) {
            startTok = token1;
          }

          if (token1.pos + token1.val.Length > endTok.pos + endTok.val.Length) {
            endTok = token1;
          }
        }

        void UpdateStartEndTokRecursive(INode? node) {
          if (node is null) {
            return;
          }

          if (node.Origin.Filepath != origin.Filepath || node is Expression { IsImplicit: true } ||
              node is DefaultValueExpression) {
            // Ignore any auto-generated expressions.
          } else {
            UpdateStartEndToken(node.StartToken);
            UpdateStartEndToken(node.EndToken);
          }
        }

        PreResolveChildren.ForEach(UpdateStartEndTokRecursive);

        if (FormatTokens != null) {
          foreach (var token in FormatTokens) {
            UpdateStartEndToken(token);
          }
        }

        origin = new SourceOrigin(startTok, endTok, tokenOrigin);
      }

      return origin;
    }
  }
}