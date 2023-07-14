using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Workspace;
using VC;

namespace Microsoft.Dafny.LanguageServer.Language {
  /// <summary>
  /// A callback interface to report verification progress
  /// </summary>
  public interface IVerificationProgressReporter {
    void RecomputeVerificationTree(CompilationAfterTranslation compilation);
    void ReportRealtimeDiagnostics(CompilationAfterTranslation compilation, bool verificationStarted);

    void ReportVerifyImplementationRunning(CompilationAfterTranslation compilation, Implementation implToken);
    void ReportEndVerifyImplementation(CompilationAfterTranslation compilation, Implementation implToken, Boogie.VerificationResult verificationResult);
    void ReportImplementationsBeforeVerification(CompilationAfterTranslation compilation, Implementation[] implementations);
    void ReportAssertionBatchResult(CompilationAfterTranslation compilation, AssertionBatchResult batchResult);
  }
}
