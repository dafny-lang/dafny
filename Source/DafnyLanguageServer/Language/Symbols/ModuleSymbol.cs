using System.Collections.Generic;
using System.Threading;

namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  public class ModuleSymbol : Symbol, ILocalizableSymbol {
    public ModuleDefinition Declaration { get; }
    public INode Node => Declaration;

    public ISet<ISymbol> Declarations { get; } = new HashSet<ISymbol>();

    public override IEnumerable<ISymbol> Children => Declarations;

    public ModuleSymbol(ISymbol? scope, ModuleDefinition moduleDefinition) : base(scope, moduleDefinition.Name) {
      Declaration = moduleDefinition;
    }

    public string GetDetailText(DafnyOptions options, CancellationToken cancellationToken) {
      return $"module {Declaration.Name}";
    }

    public override TResult Accept<TResult>(ISymbolVisitor<TResult> visitor) {
      return visitor.Visit(this);
    }
  }
}
