namespace Microsoft.Dafny.LanguageServer.Workspace.Notifications {
  /// <summary>
  /// Enumeration that identifies that actual compilation status.
  /// </summary>
  public enum CompilationStatus {
    ParsingFailed = 0,
    ResolutionFailed,
    CompilationSucceeded,
    VerificationStarted,
    VerificationFailed,
    VerificationSucceeded
  }
}
