using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.Dafny.LanguageServer.Language;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.Workspace;

public class DocumentAfterParsing : Document {
  public IReadOnlyDictionary<DocumentUri, IList<DafnyDiagnostic>> Diagnostics { get; }

  public DocumentAfterParsing(DocumentTextBuffer textDocumentItem,
    Dafny.Program program,
    IReadOnlyDictionary<DocumentUri, IList<DafnyDiagnostic>> diagnostics) : base(textDocumentItem) {
    this.Diagnostics = diagnostics;
    Program = program;
  }

  public override IEnumerable<DafnyDiagnostic> AllFileDiagnostics => FileResolutionDiagnostics;

  private IEnumerable<DafnyDiagnostic> FileResolutionDiagnostics => Diagnostics.GetOrDefault(TextDocumentItem.Uri, Enumerable.Empty<DafnyDiagnostic>);

  public Dafny.Program Program { get; }

  public override IdeState ToIdeState(IdeState previousState) {
    return previousState with {
      TextDocumentItem = TextDocumentItem,
      ResolutionDiagnostics = ComputeAllResolutionDiagnostics(),
      ImplementationsWereUpdated = false,
    };
  }

  protected IEnumerable<Diagnostic> ComputeAllResolutionDiagnostics()
  {
    var includeErrorDiagnostics = GetIncludeErrorDiagnostics();
    return FileResolutionDiagnostics.Concat(includeErrorDiagnostics).Select(d => d.ToLspDiagnostic());
  }

  private IEnumerable<DafnyDiagnostic> GetIncludeErrorDiagnostics() {
    foreach (var include in Program.Includes) {
      var messageForIncludedFile =
        Diagnostics.GetOrDefault(include.IncludedFilename, Enumerable.Empty<DafnyDiagnostic>);
      if (messageForIncludedFile.Any()) {
        var token = Program.GetFirstTopLevelToken();
        if (token == null) {
          Console.Write("");
        }
        var diagnostic = new DafnyDiagnostic(null, token, "the included file " + include.IncludedFilename.LocalPath + " contains error(s)", 
          MessageSource.Parser, ErrorLevel.Error, new DafnyRelatedInformation[] {});
        yield return diagnostic;
      }
    }
  }
}