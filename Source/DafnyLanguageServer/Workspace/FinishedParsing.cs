namespace Microsoft.Dafny.LanguageServer.Workspace;

record FinishedParsing(CompilationAfterParsing Compilation) : ICompilationEvent {
  public IdeState UpdateState(IdeState previousState) {
    return previousState with {
      Program = Compilation.Program,
      Compilation = Compilation
    };
  }
}