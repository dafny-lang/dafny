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
  public IReadOnlyDictionary<Uri, List<DafnyDiagnostic>> ResolutionDiagnostics { get; }

  public CompilationAfterParsing(Compilation compilation,
    Program program,
    IReadOnlyDictionary<Uri, List<DafnyDiagnostic>> diagnostics) : base(compilation.Version, compilation.Project, compilation.RootUris) {
    ResolutionDiagnostics = diagnostics;
    Program = program;
  }

  public Program Program { get; }

  public override IEnumerable<DafnyDiagnostic> GetDiagnostics(Uri uri) {
    return ResolutionDiagnostics.GetOrDefault(uri, Enumerable.Empty<DafnyDiagnostic>);
  }


  public override IdeState ToIdeState(IdeState previousState) {
    var baseResult = base.ToIdeState(previousState);
    return baseResult with {
      Program = Program,
      ResolutionDiagnostics = ResolutionDiagnostics.ToDictionary(
        kv => kv.Key,
        kv => (IReadOnlyList<Diagnostic>)kv.Value.Select(d => d.ToLspDiagnostic()).ToList()),
      VerificationTree = baseResult.VerificationTree ?? GetVerificationTree()
    };
  }

  public virtual VerificationTree? GetVerificationTree() {
    return Project.IsImplicitProject ? new DocumentVerificationTree(Program, Project.Uri) : null;
  }
}