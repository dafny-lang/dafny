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
    /// <param name="documentIdentifier">The text document to create the unloaded document from.</param>
    /// <param name="cancellationToken">A token to cancel the update operation before its completion.</param>
    /// <returns>The unloaded dafny document.</returns>
    /// <exception cref="System.OperationCanceledException">Thrown when the cancellation was requested before completion.</exception>
    /// <exception cref="System.ObjectDisposedException">Thrown if the cancellation token was disposed before the completion.</exception>
    IdeState CreateUnloaded(VersionedTextDocumentIdentifier documentIdentifier, CancellationToken cancellationToken);

    Task<CompilationAfterParsing> LoadAsync(DafnyOptions options, VersionedTextDocumentIdentifier documentIdentifier,
      CancellationToken cancellationToken);
  }
}
