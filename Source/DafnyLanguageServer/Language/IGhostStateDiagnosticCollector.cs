using System;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Threading;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.Language {
  /// <summary>
  /// Implementations of this interface are responsible to create diagnostics of
  /// syntax nodes that are ghost state.
  /// </summary>
  public interface IGhostStateDiagnosticCollector {
    IReadOnlyDictionary<Uri, IReadOnlyList<Range>> GetGhostStateDiagnostics(
      Program program, CancellationToken cancellationToken);
  }
}
