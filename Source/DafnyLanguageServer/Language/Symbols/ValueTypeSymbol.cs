using System.Collections.Generic;
using System.Threading;

namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  public class ValueTypeSymbol : Symbol, ILocalizableSymbol {
    public ValuetypeDecl Declaration { get; }
    public object Node => Declaration;

    public IList<ISymbol> Members { get; } = new List<ISymbol>();

    public override IEnumerable<ISymbol> Children => Members;

    public ValueTypeSymbol(ISymbol? scope, ValuetypeDecl valueTypeDeclaration) : base(scope, valueTypeDeclaration.Name) {
      Declaration = valueTypeDeclaration;
    }

    public string GetDetailText(DafnyOptions options, CancellationToken cancellationToken) {
      return Declaration.Name;
    }

    public override TResult Accept<TResult>(ISymbolVisitor<TResult> visitor) {
      return visitor.Visit(this);
    }
  }
}
