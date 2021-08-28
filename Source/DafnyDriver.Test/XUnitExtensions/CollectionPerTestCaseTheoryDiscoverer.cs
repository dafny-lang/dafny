using System;
using System.Collections.Generic;
using System.Linq;
using Xunit;
using Xunit.Abstractions;
using Xunit.Sdk;

namespace XUnitExtensions {
  public class CollectionPerTestCaseTheoryDiscoverer : IXunitTestCaseDiscoverer {
        
    readonly IXunitTestCaseDiscoverer theoryDiscoverer;

    public CollectionPerTestCaseTheoryDiscoverer(IMessageSink diagnosticMessageSink)
    {
      theoryDiscoverer = new SkippableTheoryDiscoverer(diagnosticMessageSink);
    }

    private TestCollection testCollectionForTestCase(IXunitTestCase testCase) {
      return new TestCollection(testCase.TestMethod.TestClass.TestCollection.TestAssembly, 
        (ITypeInfo) null, "Test collection for " + testCase.DisplayName);
    }

    public IEnumerable<IXunitTestCase> Discover(ITestFrameworkDiscoveryOptions discoveryOptions, ITestMethod testMethod, IAttributeInfo factAttribute) {
      // This discoverer requires pre-enumeration in order to assign a collection to each test case.
      discoveryOptions.SetValue("xunit.discovery.PreEnumerateTheories", true);
            
      var testCases = theoryDiscoverer.Discover(discoveryOptions, testMethod, factAttribute);
      
      // Select the requested fraction of the test cases if using the XUNIT_SHARD[_COUNT} environment variables.
      // Ideally this would be handled at a higher level so that cases from different test methods could be
      // balanced as a whole.
      var shardEnvVar = Environment.GetEnvironmentVariable("XUNIT_SHARD");
      var numShardsEnvVar = Environment.GetEnvironmentVariable("XUNIT_SHARD_COUNT");
      if (shardEnvVar != null || numShardsEnvVar != null) {
        if (shardEnvVar == null || numShardsEnvVar == null) {
          throw new ArgumentNullException(
            "The XUNIT_SHARD and XUNIT_SHARD_COUNT environment variables must both be provided.");
        }

        var shard = Int32.Parse(shardEnvVar);
        var numShards = Int32.Parse(numShardsEnvVar);
        if (numShards <= 0) {
          throw new ArgumentNullException(
            "XUNIT_SHARD_COUNT must be greater than 0.");
        }
        if (shard <= 0 || shard > numShards) {
          throw new ArgumentNullException(
            "XUNIT_SHARD must be at least 1 and at most XUNIT_SHARD_COUNT.");
        }
        
        var testCaseList = testCases.ToList();
        var shardStart = (shard - 1) * testCaseList.Count / numShards;
        var shardEnd = shard * testCaseList.Count / numShards;
        testCases = testCaseList.GetRange(shardStart, shardEnd - shardStart);
      }
            
      return testCases.Select(testCase => new TestCaseWithCollection(testCase, testCollectionForTestCase(testCase)));
    }
  }
}