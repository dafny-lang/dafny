using System.Collections.Generic;
using System.Threading;
using DafnyServer;
using Microsoft.Boogie;
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


    void ReportStartVerifyImplementation(Implementation implToken);
    void ReportEndVerifyImplementation(Implementation implToken, Boogie.VerificationResult verificationResult);
    int GetVerificationPriority(IToken implTok);
    void ReportImplementationsBeforeVerification(Implementation[] implementations);
    void ReportAssertionBatchResult(Split implementation,
      VCResult result);
  }
}
