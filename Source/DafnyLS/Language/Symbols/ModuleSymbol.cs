using Microsoft.Dafny;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Linq;
using System.Threading;

namespace DafnyLS.Language.Symbols {
  internal class ModuleSymbol : Symbol, ILocalizableSymbol {
    private readonly ModuleDefinition _node;

    public object Node => _node;

    public ISet<ISymbol> Declarations { get; } = new HashSet<ISymbol>();

    public override IEnumerable<ISymbol> Children => Declarations;

    public ModuleSymbol(ISymbol? scope, ModuleDefinition moduleDefinition) : base(scope, moduleDefinition.Name) {
      _node = moduleDefinition;
    }

    public DocumentSymbol AsLspSymbol(CancellationToken cancellationToken) {
      return new DocumentSymbol {
        Name = _node.Name,
        Kind = SymbolKind.Module,
        Range = new Range(_node.tok.GetLspPosition(), _node.BodyEndTok.GetLspPosition()),
        SelectionRange = GetHoverRange(),
        Detail = GetDetailText(cancellationToken),
        Children = Declarations.WithCancellation(cancellationToken).OfType<ILocalizableSymbol>().Select(child => child.AsLspSymbol(cancellationToken)).ToArray()
      };
    }

    public string GetDetailText(CancellationToken cancellationToken) {
      return $"module {_node.Name}";
    }

    public Range GetHoverRange() {
      return _node.tok.GetLspRange();
    }
  }
}
