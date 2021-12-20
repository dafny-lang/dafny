using System.Threading;

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
  }
}
