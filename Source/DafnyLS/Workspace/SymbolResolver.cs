using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Linq;
using System.Threading;

namespace DafnyLS.Workspace {
  /// <summary>
  /// Symbol resolver implementation that uses dafny-lang to resolve the symbols of a particular document.
  /// </summary>
  internal class SymbolResolver : ISymbolResolver {
    private readonly ILogger _logger;

    public SymbolResolver(ILogger<SymbolResolver> logger) {
      _logger = logger;
    }

    public IEnumerable<SymbolInformationOrDocumentSymbol> GetSymbolsFor(TextDocumentItem document, CancellationToken cancellationToken) {
      return Enumerable.Empty<SymbolInformationOrDocumentSymbol>();
    }
  }
}
