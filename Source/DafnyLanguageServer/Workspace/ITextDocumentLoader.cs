using System;
using System.Collections.Generic;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie;

namespace Microsoft.Dafny.LanguageServer.Workspace {
  /// <summary>
  /// Implementations are responsible to load a specified language server document and generate
  /// a dafny document out of it.
  /// </summary>
  public interface ITextDocumentLoader {
    /// <summary>
    /// Creates a dafny document from the given text document without loading it.
    /// </summary>
    /// <param name="textDocument">The text document to create the unloaded document from.</param>
    /// <param name="cancellationToken">A token to cancel the update operation before its completion.</param>
    /// <returns>The unloaded dafny document.</returns>
    /// <exception cref="System.OperationCanceledException">Thrown when the cancellation was requested before completion.</exception>
    /// <exception cref="System.ObjectDisposedException">Thrown if the cancellation token was disposed before the completion.</exception>
    IdeState CreateUnloaded(DocumentTextBuffer textDocument, CancellationToken cancellationToken);


    /// <summary>
    /// Loads the specified document item of the language server and applies the necessary steps
    /// to generate a dafny document instance.
    /// </summary>
    /// <param name="textDocument">The text document to load.</param>
    /// <param name="cancellationToken">A token to cancel the update operation before its completion.</param>
    /// <returns>The loaded dafny document.</returns>
    /// <exception cref="System.OperationCanceledException">Thrown when the cancellation was requested before completion.</exception>
    /// <exception cref="System.ObjectDisposedException">Thrown if the cancellation token was disposed before the completion.</exception>
    Task<DocumentAfterParsing> LoadAsync(DocumentTextBuffer textDocument, CancellationToken cancellationToken);
  }
}
