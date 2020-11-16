using System.Collections.Generic;
using System.Threading;

namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  public class ScopeSymbol : Symbol, ILocalizableSymbol {
    public BlockStmt Declaration { get; }
    public object Node => Declaration;
    public List<ISymbol> Symbols { get; } = new List<ISymbol>();
    public override IEnumerable<ISymbol> Children => Symbols;

    public ScopeSymbol(ISymbol? scope, BlockStmt declaration) : base(scope, string.Empty) {
      Declaration = declaration;
    }

    public override TResult Accept<TResult>(ISymbolVisitor<TResult> visitor) {
      return visitor.Visit(this);
    }

    public string GetDetailText(CancellationToken cancellationToken) {
      return "";
    }
  }
}
