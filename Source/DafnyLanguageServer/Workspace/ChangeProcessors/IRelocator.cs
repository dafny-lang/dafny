using System.Collections.Generic;
using System.Collections.Immutable;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Threading;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;

namespace Microsoft.Dafny.LanguageServer.Workspace.ChangeProcessors {
  /// <summary>
  /// Implementations of this interface are responsible to relocate symbols and diagnostics
  /// to their new positions according to the given <see cref="DidChangeTextDocumentParams"/>.
  /// </summary>
  public interface IRelocator {
    Position RelocatePosition(Position position, DidChangeTextDocumentParams changes, CancellationToken cancellationToken);
    Range? RelocateRange(Range range, DidChangeTextDocumentParams changes, CancellationToken cancellationToken);

    /// <summary>
    /// Relocates the symbols of the given table with the given text changes.
    /// </summary>
    /// <param name="originalSymbolTable">The symbol table whose symbols should be relocated.</param>
    /// <param name="changes">The applied changes to the text document that should be used for the relocation.</param>
    /// <param name="cancellationToken">A token to stop the relocation prior completion.</param>
    /// <returns>A new symbol table whose symbols are placed according to the given changes.</returns>
    /// <exception cref="System.OperationCanceledException">Thrown when the cancellation was requested before completion.</exception>
    /// <exception cref="System.ObjectDisposedException">Thrown if the cancellation token was disposed before the completion.</exception>
    SignatureAndCompletionTable RelocateSymbols(SignatureAndCompletionTable originalSymbolTable, DidChangeTextDocumentParams changes, CancellationToken cancellationToken);

    /// <summary>
    /// Relocates diagnostics
    /// </summary>
    /// <param name="originalDiagnostics">The diagnostics that should be relocated.</param>
    /// <param name="changes">The applied changes to the text document that should be used for the relocation.</param>
    /// <param name="cancellationToken">A token to stop the relocation prior completion.</param>
    /// <returns>A list of diagnotics whose symbols are placed according to the given changes.</returns>
    /// <exception cref="System.OperationCanceledException">Thrown when the cancellation was requested before completion.</exception>
    /// <exception cref="System.ObjectDisposedException">Thrown if the cancellation token was disposed before the completion.</exception>
    IReadOnlyList<Diagnostic> RelocateDiagnostics(IReadOnlyList<Diagnostic> originalDiagnostics, DidChangeTextDocumentParams changes, CancellationToken cancellationToken);

    /// <summary>
    /// Relocate verification trees from a document to the next document, prior to verifying the new document.
    /// That way, we can instantly publish old verifications trees for the positions in the new document
    /// </summary>
    /// <param name="oldVerificationTree">The verification tree that should be relocated, including its children</param>
    /// <param name="lines">The number of lines in the new document</param>
    /// <param name="documentChange">The applied changes to the text document that should be used for the relocation.</param>
    /// <param name="cancellationToken">A token to stop the relocation prior completion.</param>
    /// <returns></returns>
    VerificationTree RelocateVerificationTree(VerificationTree oldVerificationTree, int lines, DidChangeTextDocumentParams documentChange, CancellationToken cancellationToken);

    /// <summary>
    /// Relocate previously recorded positions from a document to the next document.
    /// </summary>
    /// <param name="originalPositions">The positions to relocate</param>
    /// <param name="documentChange">The change in the document</param>
    /// <param name="cancellationToken">A token to stop the relocation prior completion.</param>
    /// <returns></returns>
    ImmutableList<Position> RelocatePositions(ImmutableList<Position> originalPositions, DidChangeTextDocumentParams documentChange, CancellationToken cancellationToken);
  }
}
