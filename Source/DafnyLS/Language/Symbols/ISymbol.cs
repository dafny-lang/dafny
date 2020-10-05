using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace DafnyLS.Language.Symbols {
  /// <summary>
  /// Represents a resolved symbol.
  /// </summary>
  internal interface ISymbol {
    /// <summary>
    /// Converts the current symbol into its LSP counterpart.
    /// </summary>
    /// <returns>The LSP representation of this symbol.</returns>
    DocumentSymbol AsLspSymbol();
  }
}
