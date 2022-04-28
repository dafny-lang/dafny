using System.Collections.Generic;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Threading;

namespace Microsoft.Dafny.LanguageServer.Workspace.ChangeProcessors {
  /// <summary>
  /// Implementations of this interface are responsible to relocate symbols and diagnostics
  /// to their new positions according to the given <see cref="DidChangeTextDocumentParams"/>.
  /// </summary>
  public interface IRelocator {
    /// <summary>
    /// Relocates the symbols of the given table with the given text changes.
    /// </summary>
    /// <param name="originalSymbolTable">The symbol table whose symbols should be relocated.</param>
    /// <param name="changes">The applied changes to the text document that should be used for the relocation.</param>
    /// <param name="cancellationToken">A token to stop the relocation prior completion.</param>
    /// <returns>A new symbol table whose symbols are placed according to the given changes.</returns>
    /// <exception cref="System.OperationCanceledException">Thrown when the cancellation was requested before completion.</exception>
    /// <exception cref="System.ObjectDisposedException">Thrown if the cancellation token was disposed before the completion.</exception>
    SymbolTable RelocateSymbols(SymbolTable originalSymbolTable, DidChangeTextDocumentParams changes, CancellationToken cancellationToken);

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
  }
}
