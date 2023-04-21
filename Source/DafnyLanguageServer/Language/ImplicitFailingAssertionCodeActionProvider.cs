using System;
using System.Collections.Generic;
using System.Linq;
using JetBrains.Annotations;
using Microsoft.Dafny.LanguageServer.Plugins;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.Language;

/// <summary>
/// A verification quick fixers provides quick "fixes" for verification errors.
/// For now, it offers to inline a failing postcondition if its failure is
/// indicated on the '{' -- meaning there is no explicit return.
/// </summary>
class ImplicitFailingAssertionCodeActionProvider : DiagnosticDafnyCodeActionProvider {
  private DafnyOptions options;

  public ImplicitFailingAssertionCodeActionProvider(DafnyOptions options) {
    this.options = options;
  }

  protected static List<Node>? FindInnermostNodeIntersecting(Node node, Range range) {
    if (node.RangeToken.StartToken.line > 0 && !node.RangeToken.ToLspRange().Intersects(range)) {
      return null;
    }

    foreach (var child in node.PreResolveChildren) {
      var result = FindInnermostNodeIntersecting(child, range);
      if (result != null) {
        result.Add(node);
        return result;
      }
    }

    return new List<Node>() { node };
  }

  class ExplicitAssertionDafnyCodeAction : DafnyCodeAction {
    private readonly DafnyOptions options;
    private readonly Expression failingImplicitAssertion;
    private readonly Node program;
    private readonly Range selection;

    public ExplicitAssertionDafnyCodeAction(
      DafnyOptions options,
      Dafny.Program program,
      Expression failingImplicitAssertion,
      Range selection
      ) : base("Explicit failing assertion") {
      this.options = options;
      this.failingImplicitAssertion = failingImplicitAssertion;
      this.program = program;
      this.selection = selection;
    }

    public override IEnumerable<DafnyCodeActionEdit> GetEdits() {
      var nodesTillFailure = FindInnermostNodeIntersecting(program, selection);

      var suggestedEdits = new List<DafnyCodeActionEdit>();
      if (nodesTillFailure != null) {
        Node? insertionNode = null;
        for (var i = 0; i < nodesTillFailure.Count; i++) {
          var node = nodesTillFailure[i];
          var nextNode = i < nodesTillFailure.Count - 1 ? nodesTillFailure[i + 1] : null;
          if ((node is Statement or LetExpr && (node is not UpdateStmt || nextNode is not VarDeclStmt))
              || nextNode is TopLevelDecl or MemberDecl or ITEExpr or MatchExpr or NestedMatchExpr or NestedMatchCase
             ) {
            insertionNode = node;
            break;
          }
        }

        if (insertionNode == null) {
          insertionNode = nodesTillFailure[0];
        }

        var start = insertionNode.StartToken;
        var assertStr = $"assert {Printer.ExprToString(options, failingImplicitAssertion)};\n" +
                        IndentationFormatter.Whitespace(Math.Max(start.col - 1, 0));
        suggestedEdits.Add(
          new DafnyCodeActionEdit(
            new RangeToken(start, null), assertStr));
      }

      return suggestedEdits.ToArray();
    }
  }

  protected override IEnumerable<DafnyCodeAction>? GetDafnyCodeActions(IDafnyCodeActionInput input,
    DafnyDiagnostic diagnostic, Range selection) {
    var uri = input.Uri;
    if (input.Program == null || diagnostic.Source != MessageSource.Verifier) {
      return null;
    }
    var failingExpressions = new List<Expression>() { };
    input.VerificationTree.ForEach(tree => {
      if (tree is AssertionVerificationTree assertTree &&
          assertTree.Finished &&
            assertTree.Range.Intersects(selection) &&
            assertTree.StatusVerification is GutterVerificationStatus.Error or GutterVerificationStatus.Inconclusive &&
            assertTree.GetAssertion()?.Description is ProofObligationDescription.ProofObligationDescription description &&
            description.GetAssertedExpr(options) is { } assertedExpr) {
        failingExpressions.Add(assertedExpr);
      }
    });
    if (failingExpressions.Count == 0) {
      return null;
    }

    return failingExpressions.Select(failingExpression =>
      new ExplicitAssertionDafnyCodeAction(options, input.Program, failingExpression, selection)
    );
  }
}