namespace Microsoft.Dafny.LanguageServer.Language {
  /// <summary>
  /// Data class to expose the program verification results.
  /// </summary>
  /// <param name="Verified"><c>true</c> if the program was successfuly verified. <c>false</c> if no verification was run or the program has errors.</param>
  /// <param name="SerializedCounterExamples">The counter examples to disprove the program's correctness, serialized to a string.</param>
  public record VerificationResult(bool Verified, string? SerializedCounterExamples = null);
}
