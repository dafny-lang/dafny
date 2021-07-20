namespace Microsoft.Dafny.LanguageServer.Language {
  /// <summary>
  /// Data class to expose the program verification results.
  /// </summary>
  /// <param name="SerializedCounterExamples">The counter examples to disprove the program's correctness, serialized to a string.</param>
  public record VerificationResult(string? SerializedCounterExamples) {
    /// <summary>
    /// <c>true</c> if the program was successfuly verified. <c>false</c> if the program has verification errors.
    /// </summary>
    public bool Verified => SerializedCounterExamples == null;
  }
}
