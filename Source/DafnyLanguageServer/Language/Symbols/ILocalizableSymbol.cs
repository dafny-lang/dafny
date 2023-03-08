using System.Threading;
using AstNode = System.Object;

namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  /// <summary>
  /// Represents a symbol that can be localized within the document.
  /// </summary>
  public interface ILocalizableSymbol : ISymbol {
    // TODO get rid of this type.

    /// <summary>
    /// Gets the syntax node of the AST> that declared this symbol.
    /// </summary>
    AstNode Node { get; }

    /// <summary>
    /// Gets the text representation of the symbol.
    /// </summary>
    /// <param name="options"></param>
    /// <param name="cancellationToken">A token to cancel the update operation before its completion.</param>
    /// <returns>The detail text of the symbol.</returns>
    /// <exception cref="System.OperationCanceledException">Thrown when the cancellation was requested before completion.</exception>
    /// <exception cref="System.ObjectDisposedException">Thrown if the cancellation token was disposed before the completion.</exception>
    string GetDetailText(DafnyOptions options, CancellationToken cancellationToken);
  }
}
