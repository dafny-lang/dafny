namespace Microsoft.Dafny.LanguageServer.Workspace {
  /// <summary>
  /// Configuration possibilities for the automatic verification.
  /// </summary>
  public enum VerifyOnMode {
    Never,
    ChangeFile,
    ChangeProject,
    Save
  }

  public enum AutoVerification {
    Never,
    OnChange,
    OnSave
  }
}
