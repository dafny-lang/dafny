using System.Diagnostics;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using VC;

namespace Microsoft.Dafny.LanguageServer.Language {
  /// <summary>
  /// A callback interface to report verification progress
  /// </summary>
  public interface IVerificationProgressReporter {
    VerificationTree Tree { get; }
    void RecomputeVerificationTree();
    void ReportRealtimeDiagnostics(bool verificationStarted, CompilationAfterResolution compilation);

    void ReportVerifyImplementationRunning(Implementation implToken);
    void ReportEndVerifyImplementation(Implementation implToken, VerificationResult verificationResult);
    void ReportImplementationsBeforeVerification(Implementation[] implementations);
    void ReportAssertionBatchResult(AssertionBatchResult batchResult);
    void SetAllUnvisitedMethodsAsVerified();
  }
}
