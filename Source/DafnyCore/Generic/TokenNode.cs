using System.Diagnostics;
using Microsoft.Boogie;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny;

public abstract class TokenNode : Node {
  // Contains tokens that did not make it in the AST but are part of the expression,
  // Enables ranges to be correct.
  // TODO: Re-add format tokens where needed until we put all the formatting to replace the tok of every expression
  internal Token[] FormatTokens = null;

  public IOrigin tok = Token.NoToken;

  [DebuggerBrowsable(DebuggerBrowsableState.Never)]
  public IOrigin Tok => tok;

  public override IOrigin Origin {
    get {
      if (Tok is Token tokenOrigin) {

        var startTok = tok.StartToken;
        var endTok = tok.EndToken;

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

          if (node.Origin.Filepath != tok.Filepath || node is Expression { IsImplicit: true } ||
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

        tok = new SourceOrigin(startTok, endTok, tokenOrigin);
      }

      return tok;
    }
    set {
      value.Center = tok.Center;
      tok = value;
    }
  }
}