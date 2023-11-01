using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using Microsoft.Extensions.Logging;
using System.Collections.Immutable;

namespace Microsoft.Dafny.LanguageServer.Workspace;

record FinishedParsing(CompilationAfterParsing Compilation) : ICompilationEvent {
  public IdeState UpdateState(DafnyOptions options, ILogger logger, IdeState previousState) {

    var trees = previousState.VerificationTrees;

    foreach (var uri in trees.Keys) {
      trees = trees.SetItem(uri,
        GutterIconAndHoverVerificationDetailsManager.UpdateTree(options, Compilation, previousState.VerificationTrees[uri]));
    }

    var cloner = new Cloner(true, false);
    var programClone = new Program(cloner, Compilation.Program);
    return previousState with {
      Program = programClone,
      Compilation = Compilation,
      VerificationTrees = trees
    };
  }
}