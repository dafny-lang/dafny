using Microsoft.Boogie;
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

    private readonly GhostOptions options;

    public GhostStateDiagnosticCollector(IOptions<GhostOptions> options) {
      this.options = options.Value;
    }

    public IEnumerable<Diagnostic> GetGhostStateDiagnostics(SymbolTable symbolTable, CancellationToken cancellationToken) {
      if (!options.MarkStatements) {
        return Enumerable.Empty<Diagnostic>();
      }
      var visitor = new GhostStateSyntaxTreeVisitor(symbolTable.CompilationUnit.Program, cancellationToken);
      visitor.Visit(symbolTable.CompilationUnit.Program);
      return visitor.GhostDiagnostics;
    }

    private class GhostStateSyntaxTreeVisitor : SyntaxTreeVisitor {
      private readonly Dafny.Program program;
      private readonly CancellationToken cancellationToken;

      public List<Diagnostic> GhostDiagnostics { get; } = new();

      public GhostStateSyntaxTreeVisitor(Dafny.Program program, CancellationToken cancellationToken) {
        this.program = program;
        this.cancellationToken = cancellationToken;
      }

      public override void VisitUnknown(object node, IToken token) { }

      public override void Visit(Statement statement) {
        cancellationToken.ThrowIfCancellationRequested();
        if (IsGhostStatementToMark(statement)) {
          GhostDiagnostics.Add(CreateGhostDiagnostic(GetRange(statement)));
        } else {
          base.Visit(statement);
        }
      }

      private bool IsGhostStatementToMark(Statement statement) {
        return statement.IsGhost
          && IsPartOfEntryDocumentAndNoMetadata(statement.Tok);
      }


      private bool IsPartOfEntryDocumentAndNoMetadata(IToken token) {
        return token.line > 0 && program.IsPartOfEntryDocument(token);
      }

      private static Range GetRange(Statement statement) {
        return statement switch {
          UpdateStmt updateStatement => GetRange(updateStatement),
          _ => CreateRange(statement.Tok, statement.EndTok)
        };
      }

      private static Range GetRange(UpdateStmt updateStatement) {
        IToken startToken;
        if (updateStatement.Lhss.Count > 0) {
          startToken = updateStatement.Lhss[0].tok;
        } else if (updateStatement.ResolvedStatements.Count > 0) {
          // This branch handles the case where the UpdateStmt consists of an CallStmt without of left hand side.
          // otherwise, we'd only mark parentheses and the semi-colon of the CallStmt. 
          startToken = GetStartTokenFromResolvedStatement(updateStatement.ResolvedStatements[0]);
        } else {
          startToken = updateStatement.Tok;
        }
        return CreateRange(startToken, updateStatement.EndTok);
      }

      private static IToken GetStartTokenFromResolvedStatement(Statement resolvedStatement) {
        return resolvedStatement switch {
          CallStmt callStatement => callStatement.MethodSelect.tok,
          _ => resolvedStatement.Tok
        };
      }

      private static Range CreateRange(IToken startToken, IToken endToken) {
        var endPosition = endToken.GetLspPosition();
        return new Range(
          startToken.GetLspPosition(),
          endPosition with { Character = endPosition.Character + endToken.val.Length }
        );
      }

      private static Diagnostic CreateGhostDiagnostic(Range range) {
        return new Diagnostic {
          Range = range,
          Message = GhostStatementMessage,
          Severity = DiagnosticSeverity.Hint
        };
      }
    }
  }
}
