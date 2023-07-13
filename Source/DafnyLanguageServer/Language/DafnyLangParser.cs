using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System;
using System.Collections.Generic;
using System.Threading;
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
  public sealed class DafnyLangParser : IDafnyParser, IDisposable {
    private readonly DafnyOptions options;
    private readonly IFileSystem fileSystem;
    private readonly ITelemetryPublisher telemetryPublisher;
    private readonly ILogger logger;
    private readonly SemaphoreSlim mutex = new(1);
    private readonly CachingParser cachingParser;

    private DafnyLangParser(DafnyOptions options, IFileSystem fileSystem, ITelemetryPublisher telemetryPublisher, ILoggerFactory loggerFactory) {
      this.options = options;
      this.fileSystem = fileSystem;
      this.telemetryPublisher = telemetryPublisher;
      logger = loggerFactory.CreateLogger<DafnyLangParser>();
      cachingParser = new CachingParser(loggerFactory.CreateLogger<CachingParser>(), fileSystem);
    }

    /// <summary>
    /// Factory method to safely create a new instance of the parser.
    /// </summary>
    /// <param name="logger">A logger instance that may be used by this parser instance.</param>
    /// <returns>A safely created dafny parser instance.</returns>
    public static DafnyLangParser Create(DafnyOptions options, IFileSystem fileSystem, ITelemetryPublisher telemetryPublisher, ILoggerFactory loggerFactory) {
      return new DafnyLangParser(options, fileSystem, telemetryPublisher, loggerFactory);
    }

    public Program Parse(TextDocumentIdentifier document, ErrorReporter reporter,
      CancellationToken cancellationToken) {
      mutex.Wait(cancellationToken);

      var beforeParsing = DateTime.Now;
      try {
        var uri = document.Uri.ToUri();
        var result = cachingParser.ParseFiles(document.Uri.ToString(),
          new DafnyFile[]
          {
            new(reporter.Options, uri, fileSystem.ReadFile(uri))
          },
          reporter, cancellationToken);
        cachingParser.Prune();
        return result;
      }
      finally {
        telemetryPublisher.PublishTime("Parse", document.Uri.ToString(), DateTime.Now - beforeParsing);
        mutex.Release();
      }
    }

    private static Dafny.Program NewDafnyProgram(TextDocumentItem document, ErrorReporter errorReporter) {
      // Ensure that the statically kept scopes are empty when parsing a new document.
      Type.ResetScopes();
      var compilation = new CompilationData(errorReporter, new List<Include>(), new List<Uri>(),
        Sets.Empty<Uri>(), Sets.Empty<Uri>());
      return new Dafny.Program(
        document.Uri.ToString(),
        new LiteralModuleDecl(new DefaultModuleDefinition(new List<Uri>()), null, Guid.NewGuid()),
        // BuiltIns cannot be initialized without Type.ResetScopes() before.
        new SystemModuleManager(errorReporter.Options),
        errorReporter, compilation
      );
    }

    public void Dispose() {
      mutex.Dispose();
    }
  }
}
