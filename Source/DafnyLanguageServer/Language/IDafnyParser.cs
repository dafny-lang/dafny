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
    Program Parse(TextDocumentIdentifier documentIdentifier, ErrorReporter reporter,
      CancellationToken cancellationToken);
  }
}
