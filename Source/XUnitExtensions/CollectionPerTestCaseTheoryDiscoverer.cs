using System;
using System.Collections.Generic;
using System.Linq;
using Xunit.Abstractions;
using Xunit.Sdk;

namespace XUnitExtensions {
  public class CollectionPerTestCaseTheoryDiscoverer : IXunitTestCaseDiscoverer {

    private readonly IXunitTestCaseDiscoverer theoryDiscoverer;

    public CollectionPerTestCaseTheoryDiscoverer(IMessageSink diagnosticMessageSink) {
      theoryDiscoverer = new SkippableTheoryDiscoverer(diagnosticMessageSink);
    }

    private static TestCollection TestCollectionForTestCase(ITestCase testCase) {
      return new TestCollection(testCase.TestMethod.TestClass.TestCollection.TestAssembly,
        (ITypeInfo)null, "Test collection for " + testCase.DisplayName);
    }

    public IEnumerable<IXunitTestCase> Discover(ITestFrameworkDiscoveryOptions discoveryOptions, ITestMethod testMethod, IAttributeInfo factAttribute) {
      // This discoverer requires pre-enumeration in order to assign a collection to each test case.
      discoveryOptions.SetValue("xunit.discovery.PreEnumerateTheories", true);

      var testCases = theoryDiscoverer.Discover(discoveryOptions, testMethod, factAttribute);

      return testCases.Select(testCase => new FileTestCase(testCase, TestCollectionForTestCase(testCase)));
    }
  }
}