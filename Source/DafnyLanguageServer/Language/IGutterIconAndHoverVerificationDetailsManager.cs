using System;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Workspace;

namespace Microsoft.Dafny.LanguageServer.Language {
  /// <summary>
  /// A callback interface to report verification progress
  /// </summary>
  public interface IGutterIconAndHoverVerificationDetailsManager {
    void RecomputeVerificationTrees(CompilationAfterParsing compilation);
    void PublishGutterIcons(CompilationAfterParsing compilation, Uri uri, bool verificationStarted);

    void ReportImplementationsBeforeVerification(CompilationAfterResolution compilation, ICanVerify canVerify, Implementation[] implementations);
    void ReportVerifyImplementationRunning(CompilationAfterResolution compilation, Implementation implToken);
    void ReportAssertionBatchResult(CompilationAfterResolution compilation, AssertionBatchResult batchResult);
    void ReportEndVerifyImplementation(CompilationAfterResolution compilation, Implementation implToken, VerificationResult verificationResult);
    void SetAllUnvisitedMethodsAsVerified(CompilationAfterResolution compilation, ICanVerify canVerify);
  }
}
