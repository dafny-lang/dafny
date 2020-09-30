using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Threading;

namespace DafnyLS.Workspace {
  /// <summary>
  /// Implementations of this provider are responsible to resolve
  /// the symbols of the specified document.
  /// </summary>
  interface ISymbolResolver {
    /// <summary>
    /// Resolves the symbols of the specified document.
    /// </summary>
    /// <param name="document">The document to resolve the symbols of.</param>
    /// <param name="cancellationToken">A token to cancel the update operation before its completion.</param>
    /// <returns>An enumerable containing all the symbols that could be resolved of the specified document.</returns>
    IEnumerable<SymbolInformationOrDocumentSymbol> GetSymbolsFor(TextDocumentItem document, CancellationToken cancellationToken);
  }
}
