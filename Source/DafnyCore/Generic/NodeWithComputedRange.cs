#nullable enable
using System.Diagnostics;
using JetBrains.Annotations;
using Microsoft.Boogie;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Tomlyn.Syntax;

namespace Microsoft.Dafny;

public abstract class NodeWithComputedRange : Node {
  // Contains tokens that did not make it in the AST but are part of the expression,
  // Enables ranges to be correct.
  // TODO: Re-add format tokens where needed until we put all the formatting to replace the tok of every expression
  internal Token[] FormatTokens;

  private IOrigin origin;

  protected NodeWithComputedRange(IOrigin? origin = null) {
  }

  protected NodeWithComputedRange(Cloner cloner, NodeWithComputedRange original) {
    origin = cloner.Origin(original.Origin);
  }

  public void SetOrigin(IOrigin newTok) {
    origin = newTok;
  }

  public override IOrigin Origin {
    get {
      if (origin is Token tokenOrigin) {

        var startTok = Origin.StartToken;
        var endTok = Origin.EndToken;

        void UpdateStartEndToken(Token token1) {
          if (token1.Filepath != Origin.Filepath) {
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

          if (node.Origin.Filepath != Origin.Filepath || node is Expression { IsImplicit: true } ||
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
    set => origin = value;
  }
}