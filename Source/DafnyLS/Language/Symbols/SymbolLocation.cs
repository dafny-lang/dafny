using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  /// <summary>
  /// Holds all location information of a certain symbol.
  /// </summary>
  public class SymbolLocation {
    /// <summary>
    /// Gets the document uri of the containing file.
    /// </summary>
    public DocumentUri Uri { get; }

    /// <summary>
    /// Gets the range of the symbol's name.
    /// </summary>
    public Range Name { get; }

    /// <summary>
    /// Gets the complete declaration range of a symbol. For example, a class would begin with position of c
    /// of class and end with the closing curly bracket.
    /// </summary>
    public Range Declaration { get; }

    public SymbolLocation(DocumentUri uri, Range name, Range declaration) {
      Uri = uri;
      Name = name;
      Declaration = declaration;
    }
  }
}
