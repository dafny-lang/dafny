using System.Diagnostics;
using Microsoft.Boogie;

namespace Microsoft.Dafny;

class OriginWithComputedRange : OriginWrapper {
  private readonly TokenNode node;

  public OriginWithComputedRange(IOrigin center, TokenNode node) : base(center) {
    this.node = node;
  }

  public override Token StartToken => RangeToken.StartToken;
  public override Token EndToken => RangeToken.EndToken;

  public RangeToken RangeToken {
    get {
      if (node.rangeToken == null) {

        var startTok = Center;
        var endTok = Center;

        void UpdateStartEndToken(Token token1) {
          if (token1.Filepath != WrappedOrigin.Filepath) {
            return;
          }

          if (token1.pos < startTok.pos) {
            startTok = token1;
          }

          if (token1.pos + token1.val.Length > endTok.pos + endTok.val.Length) {
            endTok = token1;
          }
        }

        void UpdateStartEndTokRecursive(INode node) {
          if (node is null) {
            return;
          }

          if (node.Origin.Filepath != WrappedOrigin.Filepath || node is Expression { IsImplicit: true } ||
              node is DefaultValueExpression) {
            // Ignore any auto-generated expressions.
          } else {
            UpdateStartEndToken(node.StartToken);
            UpdateStartEndToken(node.EndToken);
          }
        }

        node.PreResolveChildren.ForEach(UpdateStartEndTokRecursive);

        if (node.FormatTokens != null) {
          foreach (var token in node.FormatTokens) {
            UpdateStartEndToken(token);
          }
        }

        node.rangeToken = new RangeToken(startTok, endTok);
      }

      return node.rangeToken;
    }
    set => node.rangeToken = value;
  }

  public override IOrigin WithVal(string newVal) {
    return new OriginWithComputedRange(Center.WithVal(newVal), node);
  }
}

public abstract class TokenNode : Node {
  // Contains tokens that did not make it in the AST but are part of the expression,
  // Enables ranges to be correct.
  // TODO: Re-add format tokens where needed until we put all the formatting to replace the tok of every expression
  internal Token[] FormatTokens = null;

  public RangeToken rangeToken;

  public IOrigin tok = Token.NoToken; // TODO rename to center

  [DebuggerBrowsable(DebuggerBrowsableState.Never)]
  public override IOrigin Tok => tok;

  public override IOrigin RangeToken {
    // TODO do not create new RangeToken.
    // Let IOrigin also get a RangeToken.
    set => rangeToken = value == null ? null : new RangeToken(value.StartToken, value.EndToken);
  }

  public override IOrigin Origin => new OriginWithComputedRange(tok, this);
}