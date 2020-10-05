using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Threading;

namespace DafnyLS.Language.Symbols {
  /// <summary>
  /// Represents a resolved symbol.
  /// </summary>
  internal interface ISymbol {
    /// <summary>
    /// Converts the current symbol into its LSP counterpart.
    /// </summary>
    /// <param name="cancellationToken">A token to cancel the update operation before its completion.</param>
    /// <returns>The LSP representation of this symbol.</returns>
    /// <exception cref="System.OperationCanceledException">Thrown when the cancellation was requested before completion.</exception>
    /// <exception cref="System.ObjectDisposedException">Thrown if the cancellation token was disposed before the completion.</exception>
    DocumentSymbol AsLspSymbol(CancellationToken cancellationToken);

    /// <summary>
    /// Gets the text representation of the symbol.
    /// </summary>
    /// <param name="cancellationToken">A token to cancel the update operation before its completion.</param>
    /// <returns>The detail text of the symbol.</returns>
    /// <exception cref="System.OperationCanceledException">Thrown when the cancellation was requested before completion.</exception>
    /// <exception cref="System.ObjectDisposedException">Thrown if the cancellation token was disposed before the completion.</exception>
    string GetDetailText(CancellationToken cancellationToken);
  }
}
