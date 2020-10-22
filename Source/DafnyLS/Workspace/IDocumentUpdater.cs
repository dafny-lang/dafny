using DafnyLS.Language;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Threading;
using System.Threading.Tasks;

namespace DafnyLS.Workspace {
  /// <summary>
  /// Implementations are responsible to carefully merge the changes from the current file state to the new file state.
  /// </summary>
  public interface IDocumentUpdater {
    /// <summary>
    /// Applies the changes to the given document.
    /// </summary>
    /// <param name="oldDocument">The document that should be altered with the given changes.</param>
    /// <param name="documentChange">A collection of successive changes. That is, each change represents a delta to the previous change.</param>
    /// <param name="cancellationToken">A token to cancel the update operation before its completion.</param>
    /// <returns>The updated dafny document.</returns>
    /// <exception cref="System.OperationCanceledException">Thrown when the cancellation was requested before completion.</exception>
    /// <exception cref="System.ObjectDisposedException">Thrown if the cancellation token was disposed before the completion.</exception>
    Task<DafnyDocument> ApplyChangesAsync(DafnyDocument oldDocument, DidChangeTextDocumentParams documentChange, CancellationToken cancellationToken);
  }
}
