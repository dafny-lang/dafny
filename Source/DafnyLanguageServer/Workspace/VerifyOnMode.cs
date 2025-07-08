namespace Microsoft.Dafny.LanguageServer.Workspace {
  /// <summary>
  /// Configuration possibilities for the automatic verification.
  /// </summary>
  public enum VerifyOnMode {
    Never,
    Change,
    ChangeProject,
    Save
  }

  public enum AutoVerification {
    Never,
    OnChange,
    OnSave
  }
}
