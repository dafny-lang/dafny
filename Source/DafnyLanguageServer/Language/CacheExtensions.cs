using System;
using System.Collections.Immutable;
using System.Diagnostics;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Logging;

namespace Microsoft.Dafny.LanguageServer.Language;

static class CacheExtensions {
  public static async Task<T> ProfileAndPruneCache<T, TKey, TValue>(this PruneIfNotUsedSinceLastPruneCache<TKey, TValue> cache,
    Func<Task<T>> useCache, ILogger logger, TelemetryPublisherBase telemetryPublisher, string programName, string activity,
    CancellationToken cancellationToken)
    where TValue : class where TKey : notnull {
    var result = await cache.UseAndPrune(useCache, cancellationToken);
    telemetryPublisher.PublishTelemetry(ImmutableDictionary<string, object>.Empty.Add("subject", "caching")
      .Add("activity", activity).Add("resource", programName).Add("hits", result.Hits).Add("pruned", result.Pruned)
      .Add("total", result.Total));

    return result.Result;
  }
}