using Microsoft.Dafny;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace DafnyLS.Language.Symbols {
  internal class LocalVariableSymbol {
    private readonly LocalVariable _node;
    
    public LocalVariableSymbol(LocalVariable localVariable) {
      _node = localVariable;
    }

    public DocumentSymbol ToLspSymbol() {
      return new DocumentSymbol {
        Name = _node.Name,
        Kind = SymbolKind.Variable,
        Range = _node.Tok.GetLspRange(),
        SelectionRange = _node.Tok.GetLspRange(),
        Detail = $"{_node.Name}:{_node.Type}"
      };
    }
  }
}
