using Microsoft.Dafny;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Linq;
using System.Threading;

namespace DafnyLS.Language.Symbols {
  internal class MethodSymbol : ISymbol {
    private readonly Method _node;
    
    public MethodSymbol(Method method) {
      _node = method;
    }

    public DocumentSymbol AsLspSymbol(CancellationToken cancellationToken) {
      return new DocumentSymbol {
        Name = _node.Name,
        Kind = SymbolKind.Method,
        Range = new Range(_node.tok.GetLspPosition(), _node.BodyEndTok.GetLspPosition()),
        SelectionRange = _node.tok.GetLspRange(),
        Detail = $"method {_node.Name}({_node.Ins.AsCommaSeperatedText()}):({_node.Outs.AsCommaSeperatedText()})",
        Children = _node.Ins.Concat(_node.Outs).Select(input => new VariableSymbol(input)).AsLspSymbols(cancellationToken).ToList()
      };
    }
  }
}
