using System;
using System.CommandLine;
using Microsoft.Extensions.Logging;
using System.Threading;
using Microsoft.Dafny.LanguageServer.Workspace;

namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  /// <summary>
  /// Symbol resolver that utilizes dafny-lang to resolve the symbols.
  /// </summary>
  /// <remarks>
  /// dafny-lang makes use of static members and assembly loading. Since thread-safety of this is not guaranteed,
  /// this resolver serializes all invocations.
  /// </remarks>
  public class DafnyLangSymbolResolver : ISymbolResolver {

    public static readonly Option<bool> UseCaching = new("--use-caching", () => true,
      "Use caching to speed up analysis done by the Dafny IDE after each text edit.") {
      IsHidden = true
    };

    private readonly ILogger logger;
    private readonly ILogger<CachingResolver> innerLogger;
    private readonly SemaphoreSlim resolverMutex = new(1);
    private readonly TelemetryPublisherBase telemetryPublisher;

    public DafnyLangSymbolResolver(ILogger<DafnyLangSymbolResolver> logger, ILogger<CachingResolver> innerLogger, TelemetryPublisherBase telemetryPublisher) {
      this.logger = logger;
      this.innerLogger = innerLogger;
      this.telemetryPublisher = telemetryPublisher;
    }

    private readonly ResolutionCache resolutionCache = new();
    public void ResolveSymbols(Compilation compilation, Program program, CancellationToken cancellationToken) {
      // TODO The resolution requires mutual exclusion since it sets static variables of classes like Microsoft.Dafny.Type.
      //      Although, the variables are marked "ThreadStatic" - thus it might not be necessary. But there might be
      //      other classes as well.
      resolverMutex.Wait(cancellationToken);
      try {
        RunDafnyResolver(compilation, program, cancellationToken);
      }
      finally {
        resolverMutex.Release();
      }
    }

    private void RunDafnyResolver(Compilation compilation, Program program, CancellationToken cancellationToken) {
      var beforeResolution = DateTime.Now;
      try {
        var resolver = program.Options.Get(UseCaching)
          ? new CachingResolver(program, innerLogger, telemetryPublisher, resolutionCache)
          : new ProgramResolver(program);
        resolver.Resolve(cancellationToken);
        if (compilation.HasErrors) {
          logger.LogDebug($"encountered errors while resolving {compilation.Project.Uri}");
        }
      }
      finally {
        telemetryPublisher.PublishTime("Resolution", compilation.Project.Uri.ToString(), DateTime.Now - beforeResolution);
      }
    }
  }
}
