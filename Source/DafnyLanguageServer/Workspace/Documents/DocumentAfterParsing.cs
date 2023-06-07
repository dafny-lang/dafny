using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.Dafny.LanguageServer.Language;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.Workspace;

public class DocumentAfterParsing : Document {
  public IReadOnlyDictionary<DocumentUri, IList<DafnyDiagnostic>> ResolutionDiagnostics { get; }

  public DocumentAfterParsing(DocumentTextBuffer textDocumentItem,
    Dafny.Program program,
    IReadOnlyDictionary<DocumentUri, IList<DafnyDiagnostic>> diagnostics) : base(textDocumentItem) {
    this.ResolutionDiagnostics = diagnostics;
    Program = program;
  }

  public override IEnumerable<DafnyDiagnostic> AllFileDiagnostics => FileResolutionDiagnostics;

  private IEnumerable<DafnyDiagnostic> FileResolutionDiagnostics => ResolutionDiagnostics.GetOrDefault(TextDocumentItem.Uri, Enumerable.Empty<DafnyDiagnostic>);

  public Dafny.Program Program { get; }

  public override IdeState ToIdeState(IdeState previousState) {
    return previousState with {
      TextDocumentItem = TextDocumentItem,
      ResolutionDiagnostics = ComputeFileAndIncludesResolutionDiagnostics(),
      ImplementationsWereUpdated = false,
    };
  }

  protected IEnumerable<Diagnostic> ComputeFileAndIncludesResolutionDiagnostics() {
    var includeErrorDiagnostics = GetIncludeErrorDiagnostics();
    return FileResolutionDiagnostics.Concat(includeErrorDiagnostics).Select(d => d.ToLspDiagnostic());
  }

  private IEnumerable<DafnyDiagnostic> GetIncludeErrorDiagnostics() {
    foreach (var include in Program.Compilation.Includes) {
      var messageForIncludedFile =
        ResolutionDiagnostics.GetOrDefault(include.IncludedFilename, Enumerable.Empty<DafnyDiagnostic>);
      if (messageForIncludedFile.Any(m => m.Level == ErrorLevel.Error)) {
        var diagnostic = new DafnyDiagnostic(null, Program.GetFirstTopLevelToken(), "the included file " + include.IncludedFilename.LocalPath + " contains error(s)",
          MessageSource.Parser, ErrorLevel.Error, new DafnyRelatedInformation[] { });
        yield return diagnostic;
      }
    }
  }
}