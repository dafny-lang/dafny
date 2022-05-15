using System;
using System.Collections.Generic;
using System.Threading;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Workspace;
using VC;

namespace Microsoft.Dafny.LanguageServer.Language {
  public record AssertionBatchResult(Split Split, VCResult Result);

  public record ProgramVerificationObjects(IReadOnlyList<IImplementationTask> Tasks, IObservable<AssertionBatchResult> BatchObserver);

  /// <summary>
  /// Implementations of this interface are responsible to verify the correctness of a program.
  /// </summary>
  public interface IProgramVerifier {
    /// <summary>
    /// Applies the program verification to the specified dafny program.
    /// </summary>
    /// <param name="document">The dafny document to verify.</param>
    /// <param name="progressReporter"></param>
    /// <returns>The result of the verification run.</returns>
    /// <exception cref="System.OperationCanceledException">Thrown when the cancellation was requested before completion.</exception>
    /// <exception cref="System.ObjectDisposedException">Thrown if the cancellation token was disposed before the completion.</exception>
    ProgramVerificationObjects GetImplementationTasks(DafnyDocument document);
  }
}
