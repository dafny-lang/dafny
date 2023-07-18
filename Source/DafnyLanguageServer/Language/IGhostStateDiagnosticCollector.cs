using Microsoft.Dafny.LanguageServer.Language.Symbols;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Threading;

namespace Microsoft.Dafny.LanguageServer.Language {
  /// <summary>
  /// Implementations of this interface are responsible to create diagnostics of
  /// syntax nodes that are ghost state.
  /// </summary>
  public interface IGhostStateDiagnosticCollector {
    /// <summary>
    /// Collects all the ghost states and creates diagnostics for the given symbol table.
    /// </summary>
    /// <param name="signatureAndCompletionTable">The symbol table to get the ghost state diagnostics from.</param>
    /// <param name="cancellationToken">A token to cancel the collection before its completion.</param>
    /// <returns>All the ghost variables and functions collected as LSP diagnostics.</returns>
    /// <exception cref="System.OperationCanceledException">Thrown when the cancellation was requested before completion.</exception>
    /// <exception cref="System.ObjectDisposedException">Thrown if the cancellation token was disposed before the completion.</exception>
    IEnumerable<Diagnostic> GetGhostStateDiagnostics(SignatureAndCompletionTable signatureAndCompletionTable, CancellationToken cancellationToken);
  }
}
