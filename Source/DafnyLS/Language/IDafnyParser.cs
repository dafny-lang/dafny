using Microsoft.Dafny;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Threading;
using System.Threading.Tasks;

namespace DafnyLS.Workspace {
  /// <summary>
  /// Interface exposing parse methods to generate a syntax tree out of an arbitrary dafny source.
  /// </summary>
  /// <remarks>
  /// Any implementation has to guarantee thread-safety of its public members.
  /// </remarks>
  internal interface IDafnyParser {
    /// <summary>
    /// Parses the specified document to generate a syntax tree.
    /// </summary>
    /// <param name="document">The document to parse.</param>
    /// <param name="errorReporter">The error reporter where any parsing messages should be logged to.</param>
    /// <param name="cancellationToken">A token to cancel the update operation before its completion.</param>
    /// <returns>The parsed document represented as a dafny program.</returns>
    Task<Microsoft.Dafny.Program> ParseAsync(TextDocumentItem document, ErrorReporter errorReporter, CancellationToken cancellationToken);
  }
}
