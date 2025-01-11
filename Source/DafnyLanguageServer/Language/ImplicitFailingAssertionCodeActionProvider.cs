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

  public static INode? GetInsertionNode(Node program, Range selection, out List<INode>? nodesSinceFailure, out bool needsIsolation) {
    nodesSinceFailure = FindInnermostNodeIntersecting(program, selection);

    needsIsolation = false;

    INode? insertionNode = null;
    if (nodesSinceFailure != null) {
      for (var i = 0; i < nodesSinceFailure.Count; i++) {
        var node = nodesSinceFailure[i];
        var nextNode = i < nodesSinceFailure.Count - 1 ? nodesSinceFailure[i + 1] : null;
        if (node is Statement or LetExpr &&
            ((node is AssignStatement or AssignSuchThatStmt && nextNode is not VarDeclStmt) ||
             (node is not AssignStatement && nextNode is not VarDeclStmt && nextNode is not AssignSuchThatStmt))) {
          insertionNode = node;
          break;
        }

        if (nextNode is TopLevelDecl or MemberDecl or ITEExpr or MatchExpr or NestedMatchExpr
            or NestedMatchCase) { // Nodes that change the path condition
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

      insertionNode ??= nodesSinceFailure[0];
    } else {
      insertionNode = null;
    }

    return insertionNode;
  }

  abstract class StatementInsertingCodeAction : DafnyCodeAction {
    protected readonly DafnyOptions options;
    protected readonly Expression failingImplicitAssertion;
    protected readonly Node program;
    protected readonly Range selection;

    public StatementInsertingCodeAction(
      DafnyOptions options,
      Node program,
      Expression failingImplicitAssertion,
      Range selection,
      string message
    ) : base(message) {
      this.options = options;
      this.failingImplicitAssertion = failingImplicitAssertion;
      this.program = program;
      this.selection = selection;
    }

    public override IEnumerable<DafnyCodeActionEdit> GetEdits() {
      var insertionNode = GetInsertionNode(program, selection, out var nodesTillFailure, out var needsIsolation);
      if (insertionNode == null || nodesTillFailure == null) {
        return new DafnyCodeActionEdit[] { };
      }

      if (insertionNode is AssertStmt or VarDeclStmt or CallStmt && insertionNode.EndToken is { val: ";" } endToken) {
        // We can insert a by block to keep the proof limited
        var start = insertionNode.StartToken;
        var indentation = IndentationFormatter.Whitespace(Math.Max(start.col - 1, 0));
        var indentation2 = indentation + "  ";
        var block = " by {\n" +
                    indentation2 + GetStatementToInsert(indentation2) + "\n" +
                    indentation + "}";
        return ReplaceWith(endToken, block);
      } else {// TODO: If there is already a by block, can we insert into it? 
        var start = insertionNode.StartToken;
        var indentation = IndentationFormatter.Whitespace(Math.Max(start.col - 1 + (needsIsolation ? 1 : 0), 0));
        var assertStr = GetStatementToInsert(indentation) + "\n" + indentation;
        return PrefixWithStatement(insertionNode, needsIsolation, assertStr);
      }
    }

    /// Helper for subclasses to print an expression
    protected string S(Expression e) {
      return Printer.ExprToString(options, e, new PrintFlags(UseOriginalDafnyNames: true));
    }

    /// Emit code editing instructions to insert the given statement before the given insertion node
    /// Wraps everything with parentheses if it requires isolationn, which is the case in expressions notably
    protected static IEnumerable<DafnyCodeActionEdit> PrefixWithStatement(INode insertionNode, bool needsIsolation, string statement) {
      var start = insertionNode.StartToken;
      if (needsIsolation) {
        statement = "(" + statement;
      }
      var suggestedEdits = new List<DafnyCodeActionEdit> {
        new (
          InsertBefore(start), statement)
      };
      if (needsIsolation) {
        suggestedEdits.Add(new DafnyCodeActionEdit(
          InsertAfter(insertionNode.EndToken), ")"));
      }

      return suggestedEdits.ToArray();
    }

    /// Emit code editing instructions to insert the given statement before the given insertion node
    /// Wraps everything with parentheses if it requires isolationn, which is the case in expressions notably
    protected static IEnumerable<DafnyCodeActionEdit> ReplaceWith(Token tokenToReplace, string block) {
      var suggestedEdits = new List<DafnyCodeActionEdit> {
        new (Replace(tokenToReplace), block)
      };

      return suggestedEdits.ToArray();
    }


    protected abstract string GetStatementToInsert(string indentation);
  }

  class ExplicitAssertionDafnyCodeAction : StatementInsertingCodeAction {
    public ExplicitAssertionDafnyCodeAction(
      DafnyOptions options,
      Node program,
      Expression failingImplicitAssertion,
      Range selection
      ) : base(options, program, failingImplicitAssertion, selection, "Insert explicit failing assertion") {
    }

    protected override string GetStatementToInsert(string indentation) {
      return $"assert {S(failingImplicitAssertion)};";
    }
  }

  class BinaryExprToCalcStatementCodeAction : StatementInsertingCodeAction {
    private readonly BinaryExpr failingExplicit;

    public BinaryExprToCalcStatementCodeAction(
      DafnyOptions options,
      Node program,
      BinaryExpr failingExplicit,
      Range selection
      ) : base(options, program, failingExplicit, selection, "Insert a calc statement") {
      this.failingExplicit = failingExplicit;
    }

    protected override string GetStatementToInsert(string i) {
      var op = failingExplicit.Op is BinaryExpr.Opcode.Iff ? "<==> " : "";
      return /*
         */$"calc {op}{{\n" +
        $"{i}  {S(failingExplicit.E0)};\n" +
        $"{i}  {S(failingExplicit.E1)};\n" +
        $"{i}}}";
    }
  }

  class ForallExprStatementCodeAction : StatementInsertingCodeAction {
    private readonly ForallExpr failingExplicit;

    public ForallExprStatementCodeAction(
      DafnyOptions options,
      Node program,
      ForallExpr failingExplicit,
      Range selection
    ) : base(options, program, failingExplicit, selection, "Insert a forall statement") {
      this.failingExplicit = failingExplicit;
    }

    protected override string GetStatementToInsert(string i) {
      return "forall " + Printer.ForallExprRangeToString(options, failingExplicit) + " ensures " + S(failingExplicit.Term) + " {\n" +
           $"{i}  assert {S(failingExplicit.Term)};\n" +
           $"{i}}}";
    }
  }

  protected override IEnumerable<DafnyCodeAction>? GetDafnyCodeActions(IDafnyCodeActionInput input,
    Diagnostic diagnostic, Range selection) {
    if (input.Program == null || diagnostic.Source != MessageSource.Verifier.ToString()) {
      return null;
    }

    var implicitlyFailing = new List<Expression>() { };
    var explicitlyFailing = new List<Expression>() { };
    input.VerificationTree?.Visit(tree => {
      if (tree is AssertionVerificationTree assertTree &&
          assertTree.Finished &&
          assertTree.Range.Intersects(selection) &&
          assertTree.StatusVerification is GutterVerificationStatus.Error or GutterVerificationStatus.Inconclusive &&
          assertTree.GetAssertion()?.Description is ProofObligationDescription description &&
          description.GetAssertedExpr(options) is { } assertedExpr) {
        if (description.IsImplicit) {
          implicitlyFailing.Add(assertedExpr);
        } else {
          explicitlyFailing.Add(assertedExpr);
        }
      }
    });
    if (implicitlyFailing.Count == 0 && explicitlyFailing.Count == 0) {
      return null;
    }

    IEnumerable<DafnyCodeAction> suggestedExplicitAssertions = implicitlyFailing.Select(failingExpression =>
      new ExplicitAssertionDafnyCodeAction(options, input.Program, failingExpression, selection)
    );
    IEnumerable<DafnyCodeAction> suggestedCalcStatements =
      explicitlyFailing.OfType<BinaryExpr>().Where(b => b.Op is BinaryExpr.Opcode.Eq or BinaryExpr.Opcode.Iff).Select(failingEquality =>
      new BinaryExprToCalcStatementCodeAction(options, input.Program, failingEquality, selection));
    IEnumerable<DafnyCodeAction> suggestedForallStatements = explicitlyFailing
      .OfType<ForallExpr>()
      .Select(failingForall =>
      new ForallExprStatementCodeAction(options, input.Program, failingForall, selection));

    return suggestedExplicitAssertions.Concat(suggestedCalcStatements).Concat(suggestedForallStatements);
  }
}