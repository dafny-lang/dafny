using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.Workspace;

public class CompilationAfterParsing : Compilation {
  public IReadOnlyDictionary<DocumentUri, List<DafnyDiagnostic>> ResolutionDiagnostics { get; }

  public CompilationAfterParsing(VersionedTextDocumentIdentifier documentIdentifier,
    Program program,
    IReadOnlyDictionary<DocumentUri, List<DafnyDiagnostic>> diagnostics) : base(documentIdentifier) {
    ResolutionDiagnostics = diagnostics;
    Program = program;
  }

  public override IEnumerable<DafnyDiagnostic> AllFileDiagnostics => FileResolutionDiagnostics;

  private IEnumerable<DafnyDiagnostic> FileResolutionDiagnostics => ResolutionDiagnostics.GetOrDefault(DocumentIdentifier.Uri, Enumerable.Empty<DafnyDiagnostic>);

  public Program Program { get; }

  public override IdeState ToIdeState(IdeState previousState) {
    var baseResult = base.ToIdeState(previousState);
    return baseResult with {
      Program = Program,
      ResolutionDiagnostics = ComputeFileAndIncludesResolutionDiagnostics(),
      VerificationTree = baseResult.VerificationTree ?? GetVerificationTree()
    };
  }

  public virtual VerificationTree GetVerificationTree() {
    return new DocumentVerificationTree(Program, DocumentIdentifier);
  }

  protected IEnumerable<Diagnostic> ComputeFileAndIncludesResolutionDiagnostics() {
    var includeErrorDiagnostics = GetIncludeErrorDiagnostics();
    return FileResolutionDiagnostics.Concat(includeErrorDiagnostics).Select(d => d.ToLspDiagnostic());
  }

  private IEnumerable<DafnyDiagnostic> GetIncludeErrorDiagnostics() {
    var graph = new Graph<Uri>();
    foreach (var edgesForUri in Program.Compilation.Includes.GroupBy(i => i.IncluderFilename)) {
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
      var errorMessages = messageForIncludedFile.Where(m => m.Level == ErrorLevel.Error);
      var firstErrorDiagnostic = errorMessages.FirstOrDefault();
      if (firstErrorDiagnostic == null) {
        continue;
      }

      var containsErrorSTheFirstOneIs = $"the included file {include.LocalPath} contains error(s). The first one is:{firstErrorDiagnostic.Message}";
      var diagnostic = new DafnyDiagnostic(null, Program.GetFirstTopLevelToken(), containsErrorSTheFirstOneIs,
        MessageSource.Parser, ErrorLevel.Error, new DafnyRelatedInformation[] { });
      yield return diagnostic;
      break;
    }
  }
}