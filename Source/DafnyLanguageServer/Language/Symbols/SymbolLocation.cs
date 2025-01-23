using System;
using OmniSharp.Extensions.LanguageServer.Protocol;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  /// <summary>
  /// Holds all location information of a certain symbol.
  /// </summary>
  public class SymbolLocation(Uri uri, Range name, Range declaration) {
    /// <summary>
    /// Gets the document uri of the containing file.
    /// </summary>
    public Uri Uri { get; } = uri;

    /// <summary>
    /// Gets the range of the symbol's name.
    /// </summary>
    public Range Name { get; } = name;

    /// <summary>
    /// Gets the complete declaration range of a symbol. For example, a class would begin with position of c
    /// of class and end with the closing curly bracket.
    /// </summary>
    public Range Declaration { get; } = declaration;
  }
}
