using System;
using System.Collections.Generic;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;

namespace Microsoft.Dafny.LanguageServer.Workspace;

public class CompilationAfterTranslation : CompilationAfterResolution {
  public CompilationAfterTranslation(
    CompilationAfterResolution compilationAfterResolution,
    IReadOnlyDictionary<Uri, List<DafnyDiagnostic>> diagnostics,
    Dictionary<Uri, VerificationTree> verificationTrees
    )
    : base(compilationAfterResolution, diagnostics,
      compilationAfterResolution.SymbolTable, compilationAfterResolution.SignatureAndCompletionTable,
      compilationAfterResolution.GhostDiagnostics,
      compilationAfterResolution.ImplementationsPerVerifiable,
      compilationAfterResolution.TranslatedModules,
      compilationAfterResolution.Counterexamples) {
      VerificationTrees = verificationTrees;
  }

  public override VerificationTree GetVerificationTree(Uri uri) {
    return VerificationTrees[uri];
  }

  public override IdeState ToIdeState(IdeState previousState) {
    return base.ToIdeState(previousState) with {
      ImplementationsWereUpdated = true,
      VerificationTrees = VerificationTrees,
    };
  }
  /// <summary>
  /// Contains the real-time status of all verification efforts.
  /// Can be migrated from a previous document
  /// The position and the range are never sent to the client.
  /// </summary>
  public Dictionary<Uri, VerificationTree> VerificationTrees { get; set; }
}