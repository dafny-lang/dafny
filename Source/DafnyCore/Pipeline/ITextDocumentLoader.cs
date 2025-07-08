#nullable enable
using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Threading;
using System.Threading.Tasks;

namespace Microsoft.Dafny {
  public record ProgramParseResult(Program Program, Dictionary<Uri, int> VersionedFiles);

  /// <summary>
  /// Implementations are responsible to load a specified language server document and generate
  /// a dafny document out of it.
  /// </summary>
  public interface ITextDocumentLoader {

    Task<ProgramParseResult> ParseAsync(Compilation compilation, CancellationToken cancellationToken);

    Task<ResolutionResult?> ResolveAsync(Compilation compilation,
      Program program,
      CancellationToken cancellationToken);
  }
}
