using System;
using System.Collections.Immutable;
using Microsoft.Dafny.LanguageServer.Workspace;

namespace Microsoft.Dafny.LanguageServer.Language;

static class CacheExtensions {
  public static T ProfileAndPruneCache<T, Key, Value>(this PruneIfNotUsedSinceLastPruneCache<Key, Value> cache,
    Func<T> useCache, ITelemetryPublisher telemetryPublisher, string programName, string activity)
    where Value : class where Key : notnull {
    var beforeTotal = cache.Count;
    var result = useCache();
    var afterCount = cache.Count;
    var added = afterCount - beforeTotal;
    cache.Prune();
    var hitsOrAdded = cache.Count;
    var hits = hitsOrAdded - added;
    telemetryPublisher.PublishTelemetry(ImmutableDictionary<string, object>.Empty.
      Add("subject", "caching").
      Add("activity", activity).
      Add("resource", programName.ToString()).
      Add("hits", hits).
      Add("total", hitsOrAdded));
    return result;
  }
}