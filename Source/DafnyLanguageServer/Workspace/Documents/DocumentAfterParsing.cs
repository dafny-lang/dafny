using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using Microsoft.Dafny.LanguageServer.Language;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.Workspace;

public class DocumentAfterParsing : Document {
  public IReadOnlyDictionary<DocumentUri, List<DafnyDiagnostic>> ResolutionDiagnostics { get; }

  public DocumentAfterParsing(DocumentTextBuffer textDocumentItem,
    Dafny.Program program,
    IReadOnlyDictionary<DocumentUri, List<DafnyDiagnostic>> diagnostics) : base(textDocumentItem) {
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
    var graph = new Graph<Uri>();
    foreach (var edgesForUri in Program.Includes.GroupBy(i => i.IncluderFilename)) {
      foreach (var edge in edgesForUri) {
        graph.AddEdge(edge.IncluderFilename, edge.IncludedFilename);
      }
    }

    var sortedSccRoots = graph.TopologicallySortedComponents();
    var sortedUris = sortedSccRoots.SelectMany(sccRoot => graph.GetSCC(sccRoot));
    var sortedUrisWithoutRoot = sortedUris.SkipLast(1);
    foreach (var include in sortedUrisWithoutRoot) {
      var messageForIncludedFile =
        ResolutionDiagnostics.GetOrDefault(include, () => (IReadOnlyList<DafnyDiagnostic>)ImmutableList<DafnyDiagnostic>.Empty);
      var errorMessages = messageForIncludedFile;
      if (errorMessages.All(m => m.Level != ErrorLevel.Error)) {
        continue;
      }

      var containsErrorSTheFirstOneIs = "the included file " + include.LocalPath + " contains error(s). The first one is:"
                                        + messageForIncludedFile.First();
      var diagnostic = new DafnyDiagnostic(null, Program.GetFirstTopLevelToken(), containsErrorSTheFirstOneIs,
        MessageSource.Parser, ErrorLevel.Error, new DafnyRelatedInformation[] { });
      yield return diagnostic;
      break;
    }
  }
}