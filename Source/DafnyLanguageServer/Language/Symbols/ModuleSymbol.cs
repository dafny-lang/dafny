using System.Collections.Generic;
using System.Threading;

namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  public class ModuleSymbol : Symbol, ILocalizableSymbol {
    public ModuleDefinition Declaration { get; }
    public INode Node => Declaration;

    public ISet<ILegacySymbol> Declarations { get; } = new HashSet<ILegacySymbol>();

    public override IEnumerable<ILegacySymbol> Children => Declarations;

    public ModuleSymbol(ILegacySymbol? scope, ModuleDefinition moduleDefinition) : base(scope, moduleDefinition.Name) {
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
