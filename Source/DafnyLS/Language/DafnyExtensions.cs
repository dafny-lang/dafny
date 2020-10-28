namespace DafnyLS.Language {
  /// <summary>
  /// Extension methods to work with elements that belong to dafny-lang.
  /// </summary>
  public static class DafnyExtensions {
    /// <summary>
    /// Checks if the given token is part of the entrypoint document.
    /// </summary>
    /// <param name="program">The dafny program to check the token against.</param>
    /// <param name="token">The token to check.</param>
    /// <returns><c>true</c> if the given token is part of the entrypoint document of the given program.</returns>
    public static bool IsPartOfEntryDocument(this Microsoft.Dafny.Program program, Microsoft.Boogie.IToken token) {
      // TODO Cleanup this check. It requires that DafnyLangParser sets the program's name to the entrypoint filename.
      // TODO the token filename happens to be null if it's representing a default module or class.
      return token.filename == null || token.filename == program.FullName;
    }
  }
}
