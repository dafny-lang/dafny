using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Threading;

namespace DafnyLS.Language.Symbols {
  /// <summary>
  /// A table containing the symbols of a dafny syntax tree.
  /// </summary>
  internal class SymbolTable {
    public IReadOnlyList<LocalVariableSymbol> Symbols { get; }

    public SymbolTable(IReadOnlyList<LocalVariableSymbol> symbols) {
      Symbols = symbols;
    }

    public IEnumerable<DocumentSymbol> ToLspSymbols(CancellationToken cancellationToken) {
      foreach(var symbol in Symbols) {
        cancellationToken.ThrowIfCancellationRequested();
        yield return symbol.ToLspSymbol();
      }
    }
  }
}
