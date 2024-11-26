using System;
using System.Diagnostics;
using Microsoft.Boogie;

namespace Microsoft.Dafny;

class TokenSourceOrigin : TokenWrapper {
  private TokenNode node;

  private RangeToken rangeToken;

  public TokenSourceOrigin(Token center, TokenNode node) : base(center) {
    this.node = node;
  }

  public RangeToken RangeToken {
    get {
      if (rangeToken == null) {

        var startTok = (Token)WrappedOrigin;
        var endTok = (Token)WrappedOrigin;

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

          if (node.RangeToken.Filepath != WrappedOrigin.Filepath || node is Expression { IsImplicit: true } ||
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

        rangeToken = new RangeToken(startTok, endTok);
      }

      return rangeToken;
    }
    set => rangeToken = value;
  }

  public override IOrigin WithVal(string newVal) {
    return new TokenSourceOrigin(Center.WithVal(newVal), node);
  }

  public Token Center => (Token)WrappedOrigin;
  public Token StartToken => RangeToken.StartToken;
  public Token EndToken => RangeToken.StartToken;
}

public abstract class TokenNode : Node {
  // Contains tokens that did not make it in the AST but are part of the expression,
  // Enables ranges to be correct.
  // TODO: Re-add format tokens where needed until we put all the formatting to replace the tok of every expression
  internal Token[] FormatTokens = null;

  protected IOrigin rangeToken = null;

  public IOrigin tok = Token.NoToken; // TODO rename to center?

  [DebuggerBrowsable(DebuggerBrowsableState.Never)]
  public override IOrigin Tok {
    get => tok;
  }
  public override IOrigin RangeToken { get => Origin;
    set => ((TokenSourceOrigin)tok.Unwrap()).RangeToken = (RangeToken)value;
  }
  public override IOrigin Origin => tok;

}