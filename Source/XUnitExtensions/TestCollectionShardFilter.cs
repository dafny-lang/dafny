using System;
using System.Collections.Generic;
using System.Linq;
using Xunit;
using Xunit.Abstractions;

namespace XUnitExtensions {
  public class TestCollectionShardFilter : ITestCollectionOrderer {
    public IEnumerable<ITestCollection> OrderTestCollections(IEnumerable<ITestCollection> testCollections) {
      var sorted = testCollections.OrderBy(c => c.DisplayName);

      // Select the requested fraction of the test collections if using the XUNIT_SHARD[_COUNT] environment variables.
      var shardEnvVar = Environment.GetEnvironmentVariable("XUNIT_SHARD");
      var numShardsEnvVar = Environment.GetEnvironmentVariable("XUNIT_SHARD_COUNT");
      if (shardEnvVar != null || numShardsEnvVar != null) {
        if (shardEnvVar == null || numShardsEnvVar == null) {
          throw InTheTowelAndExit(
            "The XUNIT_SHARD and XUNIT_SHARD_COUNT environment variables must both be provided.");
        }

        var shard = Int32.Parse(shardEnvVar);
        var numShards = Int32.Parse(numShardsEnvVar);
        if (numShards <= 0) {
          throw InTheTowelAndExit(
            "XUNIT_SHARD_COUNT must be greater than 0.");
        }
        if (shard <= 0 || shard > numShards) {
          throw InTheTowelAndExit(
            "XUNIT_SHARD must be at least 1 and at most XUNIT_SHARD_COUNT.");
        }

        return sorted.Where((_, index) => index % numShards == shard - 1);
      }

      return sorted;
    }

    // Helper method to log a message before exiting.
    // The XUnit framework doesn't consider orderers critical
    // so it will swallow our exceptions and continue.
    // The sharding is costly to silently ignore
    // so we log and exit instead.
    private InvalidOperationException InTheTowelAndExit(String message) {
      Console.Error.WriteLine(message);
      Environment.Exit(1);

      // Never actually reached, but makes the compiler happy.
      return new InvalidOperationException(message);
    }
  }
}