using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Util;
using Microsoft.Extensions.Options;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Linq;
using System.Threading;

namespace Microsoft.Dafny.LanguageServer.Language {
  /// <summary>
  /// Ghost state diagnostic collector that resolves the ghost states by recursively traversing
  /// through the given <see cref="Dafny.Program"/> instance.
  /// </summary>
  /// <remarks>
  /// To avoid diagnostic overload, the recursion will stop once a ghost state has been identified. Otherwise,
  /// diagnostics may overlap with each other, creating a large list of hover texts.
  /// </remarks>
  public class GhostStateDiagnosticCollector : IGhostStateDiagnosticCollector {
    private const string GhostStatementMessage = "Ghost statement";
    private const string GhostFunctionMessage = "Ghost function";
    private const string GhostVariableMessage = "Ghost variable";

    private readonly GhostOptions options;

    public GhostStateDiagnosticCollector(IOptions<GhostOptions> options) {
      this.options = options.Value;
    }

    public IEnumerable<Diagnostic> GetGhostStateDiagnostics(SymbolTable symbolTable, CancellationToken cancellationToken) {
      if (!options.FadeEnabled) {
        return Enumerable.Empty<Diagnostic>();
      }
      var visitor = new GhostStateSyntaxTreeVisitor(options, symbolTable.CompilationUnit.Program, cancellationToken);
      visitor.Visit(symbolTable.CompilationUnit.Program);
      return visitor.GhostDiagnostics;
    }

    private class GhostStateSyntaxTreeVisitor : SyntaxTreeVisitor {
      private readonly GhostOptions options;
      private readonly Dafny.Program program;
      private readonly CancellationToken cancellationToken;

      public List<Diagnostic> GhostDiagnostics { get; } = new();

      public GhostStateSyntaxTreeVisitor(GhostOptions options, Dafny.Program program, CancellationToken cancellationToken) {
        this.options = options;
        this.program = program;
        this.cancellationToken = cancellationToken;
      }

      public override void VisitUnknown(object node, Boogie.IToken token) { }

      public override void Visit(Function function) {
        cancellationToken.ThrowIfCancellationRequested();
        if (options.FadeDeclarations && function.IsGhost && program.IsPartOfEntryDocument(function.tok)) {
          GhostDiagnostics.Add(CreateFunctionDiagnostic(GetDeclarationRange(function)));
        } else {
          base.Visit(function);
        }
      }

      public override void Visit(Statement statement) {
        cancellationToken.ThrowIfCancellationRequested();
        if (options.FadeStatements && statement.IsGhost && IsPartOfEntryDocumentAndNoMetadata(statement.Tok)) {
          GhostDiagnostics.Add(CreateDiagnostic(
            new Range(statement.Tok.GetLspPosition(), statement.EndTok.GetLspPosition()),
            GhostStatementMessage
          ));
        } else {
          base.Visit(statement);
        }
      }

      public override void Visit(Expression expression) {
        cancellationToken.ThrowIfCancellationRequested();
        if (!options.FadeDesignators) {
          // We do not have to descend further in the tree if we do not fade designators since
          // declarations may not occur inside expressions.
          return;
        }
        if (expression.WasResolved() && IsPartOfEntryDocumentAndNoMetadata(expression.tok)) {
          if (TrackPotentialDesignatorGhost(expression.tok, expression.Resolved)) {
            return;
          }
        }
        base.Visit(expression);
      }

      private bool TrackPotentialDesignatorGhost(Boogie.IToken token, Expression resolvedExpression) {
        return resolvedExpression switch {
          MemberSelectExpr memberSelectExpression => TrackPotentialMemberDesignatorGhost(token, memberSelectExpression),
          IdentifierExpr identifierExpression => TrackPotentialVariableDesignatorGhost(token, identifierExpression),
          _ => false
        };
      }

      private bool TrackPotentialMemberDesignatorGhost(Boogie.IToken token, MemberSelectExpr memberSelectExpression) {
        if (!memberSelectExpression.Member.IsGhost) {
          return false;
        }
        switch (memberSelectExpression.Member) {
          case Function:
            GhostDiagnostics.Add(CreateFunctionDiagnostic(token.GetLspRange()));
            return true;
          case IVariable:
            GhostDiagnostics.Add(CreateVariableDiagnostic(token.GetLspRange()));
            return true;
        }
        return false;
      }

      private bool TrackPotentialVariableDesignatorGhost(Boogie.IToken token, IdentifierExpr identifierExpression) {
        if (!identifierExpression.Var.IsGhost) {
          return false;
        }
        GhostDiagnostics.Add(CreateVariableDiagnostic(token.GetLspRange()));
        return true;
      }

      private bool IsPartOfEntryDocumentAndNoMetadata(Boogie.IToken token) {
        return token.line > 0 && program.IsPartOfEntryDocument(token);
      }

      private static Range GetDeclarationRange(Function function) {
        var bodyEndPosition = function.BodyEndTok.GetLspPosition();
        return new Range(
          function.tok.GetLspPosition(),
          (bodyEndPosition.Line, bodyEndPosition.Character + 1)
        );
      }

      private static Diagnostic CreateFunctionDiagnostic(Range range) {
        return CreateDiagnostic(range, GhostFunctionMessage);
      }

      private static Diagnostic CreateVariableDiagnostic(Range range) {
        return CreateDiagnostic(range, GhostVariableMessage);
      }

      private static Diagnostic CreateDiagnostic(Range range, string message) {
        return new Diagnostic {
          Range = range,
          Tags = new[] { DiagnosticTag.Unnecessary },
          Message = message,
          Severity = DiagnosticSeverity.Hint
        };
      }
    }
  }
}
