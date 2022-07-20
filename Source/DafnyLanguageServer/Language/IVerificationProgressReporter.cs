using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Workspace;
using VC;

namespace Microsoft.Dafny.LanguageServer.Language {
  /// <summary>
  /// A callback interface to report verification progress
  /// </summary>
  public interface IVerificationProgressReporter {
    /// <summary>
    /// Report verification progress.
    /// </summary>
    /// <param name="message">A progress message (IDE will prepend “Verifying” header)</param>
    void ReportProgress(string message);

    void RecomputeVerificationTree();
    void ReportRealtimeDiagnostics(bool verificationStarted, DafnyDocument document);

    void ReportVerifyImplementationRunning(Implementation implToken);
    void ReportEndVerifyImplementation(Implementation implToken, Boogie.VerificationResult verificationResult);
    void ReportImplementationsBeforeVerification(Implementation[] implementations);
    void ReportAssertionBatchResult(AssertionBatchResult batchResult);
  }
}
