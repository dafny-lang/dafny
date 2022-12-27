using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Workspace;
using VC;

namespace Microsoft.Dafny.LanguageServer.Language {
  /// <summary>
  /// A callback interface to report verification progress
  /// </summary>
  public interface IVerificationProgressReporter {
    void RecomputeVerificationTree();
    void ReportRealtimeDiagnostics(bool verificationStarted, DocumentAfterResolution document);

    void ReportVerifyImplementationRunning(Implementation implToken);
    void ReportEndVerifyImplementation(Implementation implToken, Boogie.VerificationResult verificationResult);
    void ReportImplementationsBeforeVerification(Implementation[] implementations);
    void ReportAssertionBatchResult(AssertionBatchResult batchResult);
  }
}
