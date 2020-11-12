using System.Collections.Generic;
using System.Threading;

namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  public class ClassSymbol : Symbol, ILocalizableSymbol {
    public ClassDecl Declaration { get; }
    public object Node => Declaration;

    public IList<ISymbol> Members { get; } = new List<ISymbol>();

    public override IEnumerable<ISymbol> Children => Members;

    public ClassSymbol(ISymbol? scope, ClassDecl classDeclaration) : base(scope, classDeclaration.Name) {
      Declaration = classDeclaration;
    }

    public string GetDetailText(CancellationToken cancellationToken) {
      return $"class {Declaration.Name}";
    }

    public override TResult Accept<TResult>(ISymbolVisitor<TResult> visitor) {
      return visitor.Visit(this);
    }
  }
}
