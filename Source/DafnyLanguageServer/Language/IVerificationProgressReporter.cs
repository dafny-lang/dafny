using System.Collections.Generic;
using System.Threading;
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


    void ReportStartVerifyMethodOrFunction(Implementation implToken);
    void ReportEndVerifyMethodOrFunction(Implementation implToken, Boogie.VerificationResult verificationResult);
    void ReportVerificationStarts(List<IToken> assertionToken, IToken implToken);
    void ReportVerificationCompleted(List<IToken> assertionToken, IToken implToken, ConditionGeneration.Outcome outcome,
      int totalResource);
    void ReportErrorFindItsMethod(IToken tok, string message);
    int GetVerificationPriority(IToken implTok);
    void ReportImplementationsBeforeVerification(Implementation[] implementations);
  }
}
