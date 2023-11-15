using System;
using System.Collections.Generic;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Workspace;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using VC;

namespace Microsoft.Dafny.LanguageServer.Language {
  public record AssertionBatchResult(Implementation Implementation, VCResult Result);

  public record ProgramVerificationTasks(IReadOnlyList<IImplementationTask> Tasks);

  /// <summary>
  /// Implementations of this interface are responsible to verify the correctness of a program.
  /// </summary>
  public interface IProgramVerifier {
    Task<IReadOnlyList<IImplementationTask>> GetVerificationTasksAsync(ExecutionEngine engine,
      ResolutionResult resolution,
      ModuleDefinition moduleDefinition,
      CancellationToken cancellationToken);
  }
}
