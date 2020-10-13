using Microsoft.Dafny;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Threading;

namespace DafnyLS.Language.Symbols {
  internal class ModuleSymbol : ISymbol {
    private readonly ModuleDefinition _node;

    public string Name => _node.Name;

    public ModuleSymbol(ModuleDefinition moduleDefinition) {
      _node = moduleDefinition;
    }

    public DocumentSymbol AsLspSymbol(CancellationToken cancellationToken) {
      return new DocumentSymbol {
        Name = _node.Name,
        Kind = SymbolKind.Module,
        Range = new Range(_node.tok.GetLspPosition(), _node.BodyEndTok.GetLspPosition()),
        SelectionRange = GetHoverRange(),
        Detail = GetDetailText(cancellationToken)
        // TODO children should probably resolved with the visitor.
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
