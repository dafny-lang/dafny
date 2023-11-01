using Microsoft.Extensions.Logging;

namespace Microsoft.Dafny.LanguageServer.Workspace;

public interface ICompilationEvent {
  public IdeState UpdateState(DafnyOptions options, ILogger logger, IdeState previousState);
}