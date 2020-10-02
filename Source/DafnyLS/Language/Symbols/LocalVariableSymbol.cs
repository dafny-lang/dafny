using Microsoft.Dafny;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace DafnyLS.Language.Symbols {
  internal class LocalVariableSymbol {
    // LSP starts with line and column number 0, whereas dafny's parser starts with 1.
    // TODO move to shared ressource (DiagnosticPublisher requires the same info).
    private const int LineOffset = -1;
    private const int ColumnOffset = -1;

    private readonly LocalVariable _node;
    
    public LocalVariableSymbol(LocalVariable localVariable) {
      _node = localVariable;
    }

    public DocumentSymbol ToLspSymbol() {
      return new DocumentSymbol {
        Name = _node.Name,
        Kind = SymbolKind.Variable,
        Range = GetRange(),
        SelectionRange = GetRange(),
        Detail = $"{_node.Name}:{_node.Type}"
      };
    }

    private Range GetRange() {
      return new Range(
        new Position(_node.Tok.line + LineOffset, _node.Tok.col + ColumnOffset),
        new Position(_node.Tok.line + LineOffset, _node.Tok.col + _node.Name.Length + ColumnOffset)
      );
    }
  }
}
