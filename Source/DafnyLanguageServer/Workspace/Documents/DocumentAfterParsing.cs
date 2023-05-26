using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny.LanguageServer.Workspace;

public class DocumentAfterParsing : Document {
  private readonly IReadOnlyList<DafnyDiagnostic> parseDiagnostics;

  public DocumentAfterParsing(DocumentTextBuffer textDocumentItem,
    Dafny.Program program,
    IReadOnlyList<DafnyDiagnostic> parseDiagnostics) : base(textDocumentItem) {
    this.parseDiagnostics = parseDiagnostics;
    Program = program;
  }

  public override IEnumerable<DafnyDiagnostic> AllFileDiagnostics => parseDiagnostics;

  public Dafny.Program Program { get; }

  public override IdeState ToIdeState(IdeState previousState) {
    return previousState with {
      TextDocumentItem = TextDocumentItem,
      ResolutionDiagnostics = AllFileDiagnostics.Select(d => Util.ToLspDiagnostic(d)),
      ImplementationsWereUpdated = false,
    };
  }
}