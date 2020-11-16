using System.Collections.Generic;
using System.Threading;

namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  public class ScopeSymbol : Symbol, ILocalizableSymbol {
    public List<ISymbol> Symbols { get; } = new List<ISymbol>();
    public override IEnumerable<ISymbol> Children => Symbols;
    public object Node { get; }

    public ScopeSymbol(ISymbol? scope, object node) : base(scope, string.Empty) {
      Node = node;
    }

    public override TResult Accept<TResult>(ISymbolVisitor<TResult> visitor) {
      return visitor.Visit(this);
    }

    public string GetDetailText(CancellationToken cancellationToken) {
      return "";
    }
  }
}
