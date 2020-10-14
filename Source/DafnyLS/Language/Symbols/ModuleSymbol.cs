using Microsoft.Dafny;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Threading;

namespace DafnyLS.Language.Symbols {
  internal class ModuleSymbol : Symbol, ILocalizableSymbol {
    public ModuleDefinition Declaration { get; }
    public object Node => Declaration;

    public ISet<ISymbol> Declarations { get; } = new HashSet<ISymbol>();

    public override IEnumerable<ISymbol> Children => Declarations;

    public ModuleSymbol(ISymbol? scope, ModuleDefinition moduleDefinition) : base(scope, moduleDefinition.Name) {
      Declaration = moduleDefinition;
    }

    public string GetDetailText(CancellationToken cancellationToken) {
      return $"module {Declaration.Name}";
    }

    public Range GetHoverRange() {
      return Declaration.tok.GetLspRange();
    }

    public override TResult Accept<TResult>(ISymbolVisitor<TResult> visitor) {
      return visitor.Visit(this);
    }
  }
}
