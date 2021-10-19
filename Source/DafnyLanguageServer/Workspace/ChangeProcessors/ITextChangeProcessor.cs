using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Threading;

namespace Microsoft.Dafny.LanguageServer.Workspace.ChangeProcessors {
  /// <summary>
  /// Implementations of this interface are responsible to update a <see cref="TextDocumentItem"/> with the
  /// provided <see cref="DidChangeTextDocumentParams"/>.
  /// </summary>
  public interface ITextChangeProcessor {
    /// <summary>
    /// Applies the text changes to the given text document.
    /// </summary>
    /// <param name="originalTextDocument">The original text document to update.</param>
    /// <param name="documentChange">The document change to apply.</param>
    /// <param name="cancellationToken">A token to stop the update prior completion.</param>
    /// <returns>The updated text document.</returns>
    /// <exception cref="System.OperationCanceledException">Thrown when the cancellation was requested before completion.</exception>
    /// <exception cref="System.ObjectDisposedException">Thrown if the cancellation token was disposed before the completion.</exception>
    TextDocumentItem ApplyChange(TextDocumentItem originalTextDocument, DidChangeTextDocumentParams documentChange, CancellationToken cancellationToken);
  }
}
