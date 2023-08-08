using System;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Workspace;

namespace Microsoft.Dafny.LanguageServer.Language {
  /// <summary>
  /// A callback interface to report verification progress
  /// </summary>
  public interface IVerificationProgressReporter {
    void RecomputeVerificationTrees(CompilationAfterTranslation compilation);
    void ReportRealtimeDiagnostics(CompilationAfterTranslation compilation, Uri uri, bool verificationStarted);

    void ReportVerifyImplementationRunning(CompilationAfterTranslation compilation, Implementation implToken);
    void ReportEndVerifyImplementation(CompilationAfterTranslation compilation, Implementation implToken, VerificationResult verificationResult);
    void ReportImplementationsBeforeVerification(CompilationAfterTranslation compilation, Implementation[] implementations);
    void ReportAssertionBatchResult(CompilationAfterTranslation compilation, AssertionBatchResult batchResult);
    void SetAllUnvisitedMethodsAsVerified(CompilationAfterTranslation compilation);
  }
}
