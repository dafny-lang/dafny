using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Threading;
using System.Threading.Tasks;

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
    /// <returns>An enumerable with all the symbols that could be resolved of the specified document.</returns>
    Task<IEnumerable<SymbolInformationOrDocumentSymbol>> GetSymbolsAsync(TextDocumentItem document, CancellationToken cancellationToken);
  }
}
