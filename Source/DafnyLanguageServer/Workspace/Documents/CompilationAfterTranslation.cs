using System;
using System.Collections.Generic;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;

namespace Microsoft.Dafny.LanguageServer.Workspace;

public class CompilationAfterTranslation : CompilationAfterResolution {
  public CompilationAfterTranslation(
    CompilationAfterResolution compilationAfterResolution,
    IReadOnlyDictionary<Uri, List<DafnyDiagnostic>> diagnostics,
    VerificationTree? verificationTree
    )
    : base(compilationAfterResolution, diagnostics,
      compilationAfterResolution.SymbolTable, compilationAfterResolution.SignatureAndCompletionTable,
      compilationAfterResolution.GhostDiagnostics,
      compilationAfterResolution.ImplementationsPerVerifiable,
      compilationAfterResolution.TranslatedModules,
      compilationAfterResolution.Counterexamples) {
    VerificationTree = verificationTree;
  }

  public override VerificationTree? GetVerificationTree() {
    return VerificationTree;
  }

  public override IdeState ToIdeState(IdeState previousState) {
    return base.ToIdeState(previousState) with {
      ImplementationsWereUpdated = true,
      VerificationTree = GetVerificationTree(),
      Counterexamples = new List<Counterexample>(Counterexamples)
    };
  }
  /// <summary>
  /// Contains the real-time status of all verification efforts.
  /// Can be migrated from a previous document
  /// The position and the range are never sent to the client.
  /// </summary>
  public VerificationTree? VerificationTree { get; set; }
}