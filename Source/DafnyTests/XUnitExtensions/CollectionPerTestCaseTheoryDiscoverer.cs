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
            
      IEnumerable<IXunitTestCase> testCases = theoryDiscoverer.Discover(discoveryOptions, testMethod, factAttribute);
      var shardEnvVar = Environment.GetEnvironmentVariable("XUNIT_SHARD");
      var numShardsEnvVar = Environment.GetEnvironmentVariable("XUNIT_SHARD_COUNT");
      // TODO-RS: More careful error checking
      if (shardEnvVar != null && numShardsEnvVar != null) {
        var testCaseList = testCases.ToList();
        var shard = Int32.Parse(shardEnvVar);
        var numShards = Int32.Parse(numShardsEnvVar);
        var shardStart = (shard - 1) * testCaseList.Count / numShards;
        var shardEnd = shard * testCaseList.Count / numShards;
        testCases = testCaseList.GetRange(shardStart, shardEnd - shardStart);
      }
            
      return testCases.Select(testCase => new TestCaseWithCollection(testCase, testCollectionForTestCase(testCase)));
    }
  }
}