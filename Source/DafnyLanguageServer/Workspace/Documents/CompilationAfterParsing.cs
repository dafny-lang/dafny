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
    IReadOnlyDictionary<Uri, List<DafnyDiagnostic>> diagnostics) : base(compilation.Version, compilation.Project) {
    ResolutionDiagnostics = diagnostics;
    Program = program;
  }

  public Program Program { get; }

  public override IEnumerable<DafnyDiagnostic> GetDiagnostics(Uri uri) {
    return ResolutionDiagnostics.GetOrDefault(uri, Enumerable.Empty<DafnyDiagnostic>);
  }

  public override IdeState ToIdeState(IProjectDatabase projectManagerDatabase, IdeState previousState) {
    var baseResult = base.ToIdeState(projectManagerDatabase, previousState);
    var moduleUris = Program.DefaultModuleDef.SourceDecls.Select(m => m.Tok.Uri);
    var memberUris = Program.DefaultModuleDef.DefaultClass.Members.Select(m => m.Tok.Uri);
    var sources = moduleUris.Concat(memberUris).Distinct();
    var ownedUris = sources.Where(uri => {
      if (uri == null) {
        return false;
      }
      var uriProject = projectManagerDatabase.GetProject(uri);
      return uriProject.Equals(Project);
    }).ToHashSet();
    return baseResult with {
      Program = Program,
      OwnedUris = ownedUris,
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