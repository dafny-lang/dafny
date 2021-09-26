using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Threading;

namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  public interface ISymbolResolver {
    /// <summary>
    /// Resolves the symbols of the specified dafny syntax tree.
    /// </summary>
    /// <param name="textDocument">The document whose symbols should be resolved.</param>
    /// <param name="program">The dafny program representing the syntax tree whose symbols should be resolved.</param>
    /// <param name="cancellationToken">A token to cancel the update operation before its completion.</param>
    /// <returns>The generated symbol table.</returns>
    /// <exception cref="System.OperationCanceledException">Thrown when the cancellation was requested before completion.</exception>
    /// <exception cref="System.ObjectDisposedException">Thrown if the cancellation token was disposed before the completion.</exception>
    CompilationUnit ResolveSymbols(TextDocumentItem textDocument, Microsoft.Dafny.Program program, CancellationToken cancellationToken);
  }
}
