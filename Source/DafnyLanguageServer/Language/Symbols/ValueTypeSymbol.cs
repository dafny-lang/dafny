using System.Collections.Generic;
using System.Threading;

namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  public class ValueTypeSymbol(ILegacySymbol? scope, ValuetypeDecl valueTypeDeclaration)
    : Symbol(scope, valueTypeDeclaration.Name), ILocalizableSymbol {
    public ValuetypeDecl Declaration { get; } = valueTypeDeclaration;
    public INode Node => Declaration;

    public IList<ILegacySymbol> Members { get; } = new List<ILegacySymbol>();

    public override IEnumerable<ILegacySymbol> Children => Members;

    public string GetDetailText(DafnyOptions options, CancellationToken cancellationToken) {
      return Declaration.Name;
    }

    public override TResult Accept<TResult>(ISymbolVisitor<TResult> visitor) {
      return visitor.Visit(this);
    }
  }
}
