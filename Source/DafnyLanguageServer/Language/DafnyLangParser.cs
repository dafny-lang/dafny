using Microsoft.Extensions.Logging;
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
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
  public sealed class DafnyLangParser : IDafnyParser {
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

    public Program Parse(DafnyProject project, ErrorReporter reporter, CancellationToken cancellationToken) {
      mutex.Wait(cancellationToken);

      var beforeParsing = DateTime.Now;
      try {
        var rootSourceUris = project.GetRootSourceUris(fileSystem, options).Concat(options.CliRootSourceUris).ToList();
        List<DafnyFile> dafnyFiles = new();
        foreach (var rootSourceUri in rootSourceUris) {
          try {
            dafnyFiles.Add(new DafnyFile(reporter.Options, rootSourceUri, fileSystem.ReadFile(rootSourceUri)));
          } catch (IOException) {
            logger.LogError($"Tried to parse file {rootSourceUri} that could not be found");
          }
        }
        var result = cachingParser.ParseFiles(project.ProjectName, dafnyFiles, reporter, cancellationToken);
        cachingParser.Prune();
        return result;
      }
      finally {
        telemetryPublisher.PublishTime("Parse", project.Uri.ToString(), DateTime.Now - beforeParsing);
        mutex.Release();
      }
    }
  }
}
