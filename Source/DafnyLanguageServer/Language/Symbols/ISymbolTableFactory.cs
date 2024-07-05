using System.Threading;

namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  /// <summary>
  /// Factory definition to generate a symbol table out of a given dafny program and compilation unit.
  /// </summary>
  public interface ISymbolTableFactory {
    LegacySignatureAndCompletionTable CreateFrom(CompilationInput input,
      ResolutionResult resolutionResult,
      CancellationToken cancellationToken);
  }
}
