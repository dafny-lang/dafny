using System.Diagnostics;
using JetBrains.Annotations;
using Microsoft.Boogie;

namespace Microsoft.Dafny;

public abstract class TokenNode : Node {
  // Contains tokens that did not make it in the AST but are part of the expression,
  // Enables ranges to be correct.
  // TODO: Re-add format tokens where needed until we put all the formatting to replace the tok of every expression
  internal Token[] FormatTokens = null;

  protected IOrigin RangeOrigin = null;

  protected IOrigin tok = Token.NoToken;

  public void SetTok(IOrigin newTok) {
    tok = newTok;
  }

  [DebuggerBrowsable(DebuggerBrowsableState.Never)]
  public override IOrigin Tok => tok;

  public override IOrigin Origin {
    get {
      if (RangeOrigin == null) {

        var startTok = Tok.StartToken;
        var endTok = Tok.EndToken;

        void UpdateStartEndToken(Token token1) {
          if (token1.Filepath != Tok.Filepath) {
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

          if (node.Origin.Filepath != Tok.Filepath || node is Expression { IsImplicit: true } ||
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

        RangeOrigin = new SourceOrigin(startTok, endTok);
      }

      return RangeOrigin;
    }
    set => RangeOrigin = value;
  }
}