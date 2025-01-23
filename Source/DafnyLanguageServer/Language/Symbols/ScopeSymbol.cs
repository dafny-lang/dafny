using System.Collections.Generic;
using System.Threading;
using Microsoft.Boogie;

namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  public class ScopeSymbol(ILegacySymbol? scope, INode region) : Symbol(scope, string.Empty), ILocalizableSymbol {
    public INode Node { get; } = region;
    public readonly IOrigin BodyStartToken = region.Origin.StartToken;
    public readonly IOrigin BodyEndToken = region.Origin.EndToken;
    public List<ILegacySymbol> Symbols { get; } = [];
    public override IEnumerable<ILegacySymbol> Children => Symbols;

    public override TResult Accept<TResult>(ISymbolVisitor<TResult> visitor) {
      return visitor.Visit(this);
    }

    public string GetDetailText(DafnyOptions options, CancellationToken cancellationToken) {
      return "";
    }
  }
}
