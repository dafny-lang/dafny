using Microsoft.Dafny;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Linq;
using System.Threading;

namespace DafnyLS.Language.Symbols {
  internal class FunctionSymbol : ISymbol {
    private readonly Function _node;

    public string Name => _node.Name;

    public FunctionSymbol(Function function) {
      _node = function;
    }

    public DocumentSymbol AsLspSymbol(CancellationToken cancellationToken) {
      return new DocumentSymbol {
        Name = _node.Name,
        Kind = SymbolKind.Method,
        Range = new Range(_node.tok.GetLspPosition(), _node.BodyEndTok.GetLspPosition()),
        SelectionRange = GetHoverRange(),
        Detail = GetDetailText(cancellationToken),
        Children = _node.Formals.Select(input => new VariableSymbol(input)).AsLspSymbols(cancellationToken).ToList()
      };
    }

    public string GetDetailText(CancellationToken cancellationToken) {
      return $"function {_node.Name}({_node.Formals.AsCommaSeperatedText()}):{_node.ResultType.AsText()}";
    }

    public Range GetHoverRange() {
      return _node.tok.GetLspRange();
    }
  }
}