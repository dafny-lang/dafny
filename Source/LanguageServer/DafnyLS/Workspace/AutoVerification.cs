namespace Microsoft.Dafny.LanguageServer.Workspace {
  /// <summary>
  /// Configuration possibilities for the automatic verification.
  /// </summary>
  public enum AutoVerification {
    Never,
    OnChange,
    OnSave
  }
}
