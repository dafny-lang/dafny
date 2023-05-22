using System;
using System.Threading;
using Microsoft.Dafny.LanguageServer.Workspace;

namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  /// <summary>
  /// Factory definition to generate a symbol table out of a given dafny program and compilation unit.
  /// </summary>
  public interface ISymbolTableFactory {
    /// <summary>
    /// Initializes a new symbol table with the given compilation unit.
    /// </summary>
    /// <param name="program">The parsed dafny program.</param>
    /// <param name="compilationUnit">The compilation to create the symbol table of.</param>
    /// <param name="cancellationToken">A token to cancel the update operation before its completion.</param>
    /// <returns>A symbol table representing the provided compilation unit.</returns>
    /// <exception cref="System.OperationCanceledException">Thrown when the cancellation was requested before completion.</exception>
    /// <exception cref="System.ObjectDisposedException">Thrown if the cancellation token was disposed before the completion.</exception>
    SignatureAndCompletionTable CreateFrom(CompilationUnit compilationUnit, CancellationToken cancellationToken);
    SymbolTable CreateFrom(Dafny.Program program, Document document, CancellationToken cancellationToken);
  }
}
