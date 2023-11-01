using Microsoft.Extensions.Logging;

namespace Microsoft.Dafny.LanguageServer.Workspace;

record FinishedParsing(CompilationAfterParsing Compilation) : ICompilationEvent {
  public IdeState UpdateState(DafnyOptions options, ILogger logger, IdeState previousState) {

    var trees = previousState.VerificationTrees;
    foreach (var uri in trees.Keys) {
      trees = trees.SetItem(uri,
        GutterIconAndHoverVerificationDetailsManager.UpdateTree(options, Compilation, previousState.VerificationTrees[uri]));
    }

    return previousState with {
      Program = Compilation.Program,
      Compilation = Compilation,
      VerificationTrees = trees
    };
  }
}