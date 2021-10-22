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


      private bool IsPartOfEntryDocumentAndNoMetadata(Boogie.IToken token) {
        return token.line > 0 && program.IsPartOfEntryDocument(token);
      }

      private static Diagnostic CreateDiagnostic(Range range, string message) {
        return new Diagnostic {
          Range = range,
          Message = message,
          Severity = DiagnosticSeverity.Hint
        };
      }
    }
  }
}
