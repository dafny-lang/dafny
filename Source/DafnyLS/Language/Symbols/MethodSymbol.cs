using Microsoft.Dafny;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Linq;
using System.Threading;

namespace DafnyLS.Language.Symbols {
  internal class MethodSymbol : ISymbol {
    private readonly Method _node;

    public string Name => _node.Name;

    public MethodSymbol(Method method) {
      _node = method;
    }

    public DocumentSymbol AsLspSymbol(CancellationToken cancellationToken) {
      return new DocumentSymbol {
        Name = _node.Name,
        Kind = SymbolKind.Method,
        Range = new Range(_node.tok.GetLspPosition(), _node.BodyEndTok.GetLspPosition()),
        SelectionRange = GetHoverRange(),
        Detail = GetDetailText(cancellationToken),
        Children = _node.Ins.Concat(_node.Outs).Select(input => new VariableSymbol(input)).AsLspSymbols(cancellationToken).ToList()
      };
    }

    public string GetDetailText(CancellationToken cancellationToken) {
      return $"method {_node.Name}({_node.Ins.AsCommaSeperatedText()}):({_node.Outs.AsCommaSeperatedText()})";
    }

    public Range GetHoverRange() {
      return _node.tok.GetLspRange();
    }
  }
}
