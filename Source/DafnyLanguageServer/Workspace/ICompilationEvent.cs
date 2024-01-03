using System.Threading.Tasks;
using Microsoft.Extensions.Logging;

namespace Microsoft.Dafny.LanguageServer.Workspace;

public interface ICompilationEvent {
  public Task<IdeState> UpdateState(DafnyOptions options, ILogger logger, IProjectDatabase projectDatabase,
    IdeState previousState);
}