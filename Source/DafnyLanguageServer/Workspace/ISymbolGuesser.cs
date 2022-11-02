using Microsoft.Dafny.LanguageServer.Language.Symbols;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Diagnostics.CodeAnalysis;
using System.Threading;

namespace Microsoft.Dafny.LanguageServer.Workspace {
  /// <summary>
  /// Implementations of this interface are responsible to guess the symbol at a given location.
  /// </summary>
  public interface ISymbolGuesser {
    /// <summary>
    /// Tries to resolve the symbol that is right before the given position.
    /// </summary>
    /// <param name="state">The document to query.</param>
    /// <param name="position">The desired position.</param>
    /// <param name="cancellationToken">A token to cancel the update operation before its completion.</param>
    /// <param name="symbol">The symbol in front of the given position or <c>null</c> if no such symbol exists or it could not be resolved.</param>
    /// <returns><c>true</c> if a symbol could be resolved.</returns>
    /// <exception cref="System.OperationCanceledException">Thrown when the cancellation was requested before completion.</exception>
    /// <exception cref="System.ObjectDisposedException">Thrown if the cancellation token was disposed before the completion.</exception>
    bool TryGetSymbolBefore(IdeState state, Position position, CancellationToken cancellationToken, [NotNullWhen(true)] out ISymbol? symbol);

    /// <summary>
    /// Tries to resolve the type of the symbol that is right before the given position.
    /// </summary>
    /// <param name="state">The document to query.</param>
    /// <param name="position">The desired position.</param>
    /// <param name="cancellationToken">A token to cancel the update operation before its completion.</param>
    /// <param name="typeSymbol">The symbol representing the type in front of the given position or <c>null</c> if no such symbol exists or it could not be resolved.</param>
    /// <returns><c>true</c> if a type symbol could be resolved.</returns>
    /// <exception cref="System.OperationCanceledException">Thrown when the cancellation was requested before completion.</exception>
    /// <exception cref="System.ObjectDisposedException">Thrown if the cancellation token was disposed before the completion.</exception>
    bool TryGetTypeBefore(IdeState state, Position position, CancellationToken cancellationToken, [NotNullWhen(true)] out ISymbol? typeSymbol);
  }
}
