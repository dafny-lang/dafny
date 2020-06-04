using System.Collections.Generic;
using System.Linq;
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
            return theoryDiscoverer.Discover(discoveryOptions, testMethod, factAttribute)
                                   .Select(testCase => new TestCaseWithCollection(testCase, testCollectionForTestCase(testCase)));
        }
    }
}