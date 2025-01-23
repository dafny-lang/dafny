using System.Collections.Generic;
using System.Threading;

namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  public class ModuleSymbol(ILegacySymbol? scope, ModuleDefinition moduleDefinition)
    : Symbol(scope, moduleDefinition.Name), ILocalizableSymbol {
    public ModuleDefinition Declaration { get; } = moduleDefinition;
    public INode Node => Declaration;

    public ISet<ILegacySymbol> Declarations { get; } = new HashSet<ILegacySymbol>();

    public override IEnumerable<ILegacySymbol> Children => Declarations;

    public string GetDetailText(DafnyOptions options, CancellationToken cancellationToken) {
      return $"module {Declaration.Name}";
    }

    public override TResult Accept<TResult>(ISymbolVisitor<TResult> visitor) {
      return visitor.Visit(this);
    }
  }
}
