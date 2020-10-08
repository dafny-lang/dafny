using Microsoft.Boogie;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Threading;

namespace DafnyLS.Language.Symbols {
  /// <summary>
  /// This is an auxiliary symbol that is used instead of an actual symbol to have a pointer to
  /// the declaration of the symbol.
  /// </summary>
  internal class ReferenceSymbol : ISymbol {
    // TODO In the future it could be necessary to seperate references from symbols, i.e. when the interface requires many
    //      information irrelevant to a reference.
    private readonly ISymbol _referencedSymbol;
    private readonly IToken _token;

    public string Name => _referencedSymbol.Name;

    /// <summary>
    /// Creates a new reference to an existing symbol.
    /// </summary>
    /// <param name="token">The underlying token that references the specified symbol.</param>
    /// <param name="referencedSymbol">The symbol that is referenced by the token.</param>
    public ReferenceSymbol(IToken token, ISymbol referencedSymbol) {
      _referencedSymbol = referencedSymbol;
      _token = token;
    }

    public DocumentSymbol AsLspSymbol(CancellationToken cancellationToken) => _referencedSymbol.AsLspSymbol(cancellationToken);

    public string GetDetailText(CancellationToken cancellationToken) => _referencedSymbol.GetDetailText(cancellationToken);

    public Range GetHoverRange() => _token.GetLspRange();
  }
}
