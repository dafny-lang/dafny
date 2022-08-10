using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.Plugins;

public interface IDafnyCodeActionInput {
  /// <summary>
  /// The URI of the document being considered
  /// </summary>
  string Uri { get; }
  /// <summary>
  /// The version of the document being considered. Always increasing
  /// If it did not change, it guarantees that Code is the same.
  /// This might be helpful for caching any pre-computation.
  /// </summary>
  int Version { get; }
  string Code { get; }
  Dafny.Program? Program { get; }
  Diagnostic[] Diagnostics { get; }
  string Extract(Range range);
}
