using System;
using System.Collections.Generic;
using System.Linq;
using JetBrains.Annotations;
using Microsoft.Dafny.LanguageServer.Handlers;
using Microsoft.Dafny.LanguageServer.Plugins;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.Language;

/// <summary>
/// A verification quick fixers provides quick "fixes" for verification errors.
/// For now, it offers to inline a failing postcondition if its failure is
/// indicated on the '{' -- meaning there is no explicit return.
/// </summary>
class ImplicitFailingAssertionCodeActionProvider : DiagnosticDafnyCodeActionProvider {
  private readonly DafnyOptions options;

  public ImplicitFailingAssertionCodeActionProvider(ILogger<DafnyCodeActionHandler> logger, DafnyOptions options) : base(logger) {
    this.options = options;
  }

  protected static List<INode>? FindInnermostNodeIntersecting(INode node, Range range) {
    if (node.StartToken.line > 0 && !node.Origin.ToLspRange().Intersects(range)) {
      return null;
    }

    foreach (var child in node.PreResolveChildren) {
      var result = FindInnermostNodeIntersecting(child, range);
      if (result != null) {
        result.Add(node);
        return result;
      }
    }

    return node.StartToken.line > 0 ? new List<INode> { node } : null;
  }

  class ExplicitAssertionDafnyCodeAction : DafnyCodeAction {
    private readonly DafnyOptions options;
    private readonly Expression failingImplicitAssertion;
    private readonly Node program;
    private readonly Range selection;

    public ExplicitAssertionDafnyCodeAction(
      DafnyOptions options,
      Node program,
      Expression failingImplicitAssertion,
      Range selection
      ) : base("Insert explicit failing assertion") {
      this.options = options;
      this.failingImplicitAssertion = failingImplicitAssertion;
      this.program = program;
      this.selection = selection;
    }

    public override IEnumerable<DafnyCodeActionEdit> GetEdits() {
      var nodesTillFailure = FindInnermostNodeIntersecting(program, selection);

      var suggestedEdits = new List<DafnyCodeActionEdit>();
      var needsIsolation = false;
      if (nodesTillFailure == null) {
        return suggestedEdits.ToArray();
      }

      INode? insertionNode = null;
      for (var i = 0; i < nodesTillFailure.Count; i++) {
        var node = nodesTillFailure[i];
        var nextNode = i < nodesTillFailure.Count - 1 ? nodesTillFailure[i + 1] : null;
        if (node is Statement or LetExpr &&
            ((node is AssignStatement or AssignSuchThatStmt && nextNode is not VarDeclStmt) ||
            (node is not AssignStatement && nextNode is not VarDeclStmt && nextNode is not AssignSuchThatStmt))) {
          insertionNode = node;
          break;
        }

        if (nextNode is TopLevelDecl or MemberDecl or ITEExpr or MatchExpr or NestedMatchExpr
            or NestedMatchCase) {
          insertionNode = node;
          break;
        }

        if (nextNode is BinaryExpr { Op: var op } binaryExpr &&
            ((op == BinaryExpr.Opcode.Imp && node == binaryExpr.E1) ||
             (op == BinaryExpr.Opcode.Exp && node == binaryExpr.E1) ||
             (op == BinaryExpr.Opcode.And && node == binaryExpr.E1) ||
             (op == BinaryExpr.Opcode.Or && node == binaryExpr.E1))) {
          insertionNode = node;
          needsIsolation = (op == BinaryExpr.Opcode.Exp && node == binaryExpr.E1);
          break;
        }
      }

      insertionNode ??= nodesTillFailure[0];

      var start = insertionNode.StartToken;
      var assertStr = $"{(needsIsolation ? "(" : "")}assert {Printer.ExprToString(options, failingImplicitAssertion, new PrintFlags(UseOriginalDafnyNames: true))};\n" +
                      IndentationFormatter.Whitespace(Math.Max(start.col - 1 + (needsIsolation ? 1 : 0), 0));
      suggestedEdits.Add(
        new DafnyCodeActionEdit(
          InsertBefore(start), assertStr));
      if (needsIsolation) {
        suggestedEdits.Add(new DafnyCodeActionEdit(
            InsertAfter(insertionNode.EndToken), ")"));
      }

      return suggestedEdits.ToArray();
    }
  }

  protected override IEnumerable<DafnyCodeAction>? GetDafnyCodeActions(IDafnyCodeActionInput input,
    Diagnostic diagnostic, Range selection) {
    if (input.Program == null || diagnostic.Source != MessageSource.Verifier.ToString()) {
      return null;
    }

    var failingExpressions = new List<Expression>() { };
    input.VerificationTree?.Visit(tree => {
      if (tree is AssertionVerificationTree assertTree &&
          assertTree.Finished &&
            assertTree.Range.Intersects(selection) &&
            assertTree.StatusVerification is GutterVerificationStatus.Error or GutterVerificationStatus.Inconclusive &&
            assertTree.GetAssertion()?.Description is ProofObligationDescription description &&
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