using Microsoft.Extensions.Logging;
using System;
using System.Collections.Generic;
using System.IO;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Workspace;

namespace Microsoft.Dafny.LanguageServer.Language {
  /// <summary>
  /// Parser implementation that makes use of the parse of dafny-lang. It may only be initialized exactly once since
  /// it requires initial setup of static members.
  /// </summary>
  /// <remarks>
  /// dafny-lang makes use of static members and assembly loading. Since thread-safety of this is not guaranteed,
  /// this parser serializes all invocations.
  /// </remarks>
  public sealed class DafnyLangParser : IDafnyParser {
    private readonly DafnyOptions options;
    private readonly IFileSystem fileSystem;
    private readonly TelemetryPublisherBase telemetryPublisher;
    private readonly ILogger<DafnyLangParser> logger;
    private readonly SemaphoreSlim mutex = new(1);
    private readonly ProgramParser programParser;

    public DafnyLangParser(DafnyOptions options, IFileSystem fileSystem, TelemetryPublisherBase telemetryPublisher,
      ILogger<DafnyLangParser> logger, ILogger<CachingParser> innerParserLogger) {
      this.options = options;
      this.fileSystem = fileSystem;
      this.telemetryPublisher = telemetryPublisher;
      this.logger = logger;
      programParser = options.Get(DafnyLangSymbolResolver.UseCaching)
        ? new CachingParser(innerParserLogger, fileSystem, telemetryPublisher)
        : new ProgramParser(innerParserLogger, fileSystem);
    }

    public async Task<ProgramParseResult> Parse(Compilation compilation, CancellationToken cancellationToken) {
      await mutex.WaitAsync(cancellationToken);

      var rootFiles = await compilation.RootFiles;
      var beforeParsing = DateTime.Now;
      try {
        return await programParser.ParseFiles(compilation.Project.ProjectName, rootFiles, compilation.Reporter, cancellationToken);
      }
      finally {
        telemetryPublisher.PublishTime("Parse", compilation.Project.Uri.ToString(), DateTime.Now - beforeParsing);
        mutex.Release();
      }
    }
  }
}
