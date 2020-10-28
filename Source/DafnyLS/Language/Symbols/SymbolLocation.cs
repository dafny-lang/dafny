using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace DafnyLS.Language.Symbols {
  /// <summary>
  /// Holds all location information of a certain symbol.
  /// </summary>
  public class SymbolLocation {
    /// <summary>
    /// Gets the document uri of the containing file.
    /// </summary>
    public DocumentUri Uri { get; }

    /// <summary>
    /// Gets the range of the symbol's identifier.
    /// </summary>
    public Range Identifier { get; }

    /// <summary>
    /// Gets the complete declaration range of a symbol. For example, a class would begin with position of c
    /// of class and end with the closing curly bracket.
    /// </summary>
    public Range Declaration { get; }

    public SymbolLocation(DocumentUri uri, Range identifier, Range declaration) {
      Uri = uri;
      Identifier = identifier;
      Declaration = declaration;
    }
  }
}
