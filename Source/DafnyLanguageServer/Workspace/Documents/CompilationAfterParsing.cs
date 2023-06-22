using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using Microsoft.Dafny.LanguageServer.Language;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.Workspace;

public class CompilationAfterParsing : Compilation {
  public IReadOnlyDictionary<Uri, List<DafnyDiagnostic>> ResolutionDiagnostics { get; }

  public CompilationAfterParsing(Compilation compilation,
    Program program,
    IReadOnlyDictionary<Uri, List<DafnyDiagnostic>> diagnostics) : base(compilation.Version, compilation.Project) 
  {
    ResolutionDiagnostics = diagnostics;
    Program = program;
  }

  public Program Program { get; }

  public override IdeState ToIdeState(IdeState previousState) {
    return previousState with {
      Program = Program,
      ResolutionDiagnostics = ResolutionDiagnostics.ToDictionary(
        kv => kv.Key, 
        kv => (IReadOnlyList<Diagnostic>)kv.Value.Select(d => d.ToLspDiagnostic()).ToList()),
      ImplementationsWereUpdated = false,
    };
  }

  // protected IEnumerable<Diagnostic> ComputeFileAndIncludesResolutionDiagnostics() {
  //   var includeErrorDiagnostics = GetIncludeErrorDiagnostics();
  //   return FileResolutionDiagnostics.Concat(includeErrorDiagnostics).Select(d => d.ToLspDiagnostic());
  // }
  //
  // private IEnumerable<DafnyDiagnostic> GetIncludeErrorDiagnostics() {
  //   var graph = new Graph<Uri>();
  //   foreach (var edgesForUri in Program.Compilation.Includes.GroupBy(i => i.IncluderFilename)) {
  //     foreach (var edge in edgesForUri) {
  //       graph.AddEdge(edge.IncluderFilename, edge.IncludedFilename);
  //     }
  //   }
  //
  //   var sortedSccRoots = graph.TopologicallySortedComponents();
  //   var sortedUris = sortedSccRoots.SelectMany(sccRoot => graph.GetSCC(sccRoot));
  //   var sortedUrisWithoutRoot = sortedUris.SkipLast(1);
  //   foreach (var include in sortedUrisWithoutRoot) {
  //     var messageForIncludedFile =
  //       ResolutionDiagnostics.GetOrDefault(include, () => (IReadOnlyList<DafnyDiagnostic>)ImmutableList<DafnyDiagnostic>.Empty);
  //     var errorMessages = messageForIncludedFile.Where(m => m.Level == ErrorLevel.Error);
  //     var firstErrorMessage = errorMessages.FirstOrDefault();
  //     if (firstErrorMessage == null) {
  //       continue;
  //     }
  //
  //     var containsErrorSTheFirstOneIs = $"the included file {include.LocalPath} contains error(s). The first one is:{firstErrorMessage}";
  //     var diagnostic = new DafnyDiagnostic(null, Program.GetFirstTopLevelToken(), containsErrorSTheFirstOneIs,
  //       MessageSource.Parser, ErrorLevel.Error, new DafnyRelatedInformation[] { });
  //     yield return diagnostic;
  //     break;
  //   }
  // }
}