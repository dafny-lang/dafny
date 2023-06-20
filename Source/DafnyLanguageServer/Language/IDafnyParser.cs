using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Threading;
using Microsoft.Dafny.LanguageServer.Workspace;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;

namespace Microsoft.Dafny.LanguageServer.Language {
  /// <summary>
  /// Interface exposing parse methods to generate a syntax tree out of an arbitrary dafny source.
  /// </summary>
  /// <remarks>
  /// Any implementation has to guarantee thread-safety of its public members.
  /// </remarks>
  public interface IDafnyParser {
    /// <summary>
    /// Creates a new dafny program without parsing the given text document.
    /// </summary>
    /// <param name="textDocument">The document to create the "empty" dafny program from.</param>
    /// <param name="errorReporter">The error reporter to attach to the dafny program.</param>
    /// <param name="cancellationToken">A token to cancel the creation operation before its completion.</param>
    /// <returns>An "empty" dafny program representing the given text document.</returns>
    /// <exception cref="System.OperationCanceledException">Thrown when the cancellation was requested before completion.</exception>
    /// <exception cref="System.ObjectDisposedException">Thrown if the cancellation token was disposed before the completion.</exception>
    Dafny.Program CreateUnparsed(TextDocumentItem textDocument, ErrorReporter errorReporter, CancellationToken cancellationToken);

    Program Parse(TextDocumentIdentifier documentIdentifier, IFileSystem fileSystem, ErrorReporter reporter,
      CancellationToken cancellationToken);
  }
}
