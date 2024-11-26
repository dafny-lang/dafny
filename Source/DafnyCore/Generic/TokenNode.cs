using System.Diagnostics;
using Microsoft.Boogie;

namespace Microsoft.Dafny;

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

  public override IOrigin RangeToken {
    get {
      if (rangeToken == null) {

        var startTok = (Token)tok.Unwrap();
        var endTok = tok.Unwrap();

        void UpdateStartEndToken(Token token1) {
          if (token1.Filepath != tok.Filepath) {
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

          if (node.RangeToken.Filepath != tok.Filepath || node is Expression { IsImplicit: true } ||
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

        rangeToken = new RangeToken(startTok, endTok);
      }

      return rangeToken;
    }
    set => rangeToken = value;
  }
}