using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace DafnyLS.Language.Symbols {
  /// <summary>
  /// Holds all location information of a certain symbol.
  /// </summary>
  public class SymbolLocation {
    /// <summary>
    /// Gets the range of the symbol's identifier.
    /// </summary>
    public Range Identifier { get; }

    /// <summary>
    /// Gets the complete declaration range of a symbol. For example, a class would begin with position of c
    /// of class and end with the closing curly bracket.
    /// </summary>
    public Range Declaration { get; }

    public SymbolLocation(Range identifier, Range declaration) {
      Identifier = identifier;
      Declaration = declaration;
    }
  }
}
