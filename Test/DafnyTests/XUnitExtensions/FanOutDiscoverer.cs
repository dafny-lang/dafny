using System;
using Xunit.Abstractions;
using Xunit.Sdk;

namespace DefaultNamespace {
    public class FanOutDiscoverer : TestFrameworkDiscoverer {
        readonly CollectionPerClassTestCollectionFactory testCollectionFactory;

        public FanOutDiscoverer(IAssemblyInfo assemblyInfo, ISourceInformationProvider sourceProvider, IMessageSink diagnosticMessageSink) : base(assemblyInfo, sourceProvider, diagnosticMessageSink) {
            var testAssembly = new TestAssembly(assemblyInfo, AppDomain.CurrentDomain.SetupInformation.ConfigurationFile);
            testCollectionFactory = new CollectionPerClassTestCollectionFactory(testAssembly, diagnosticMessageSink);
        }

        protected override ITestClass CreateTestClass(ITypeInfo @class) {
            return new TestClass(testCollectionFactory.Get(@class), @class);
        }

        protected override bool FindTestsForType(ITestClass testClass, bool includeSourceInformation, IMessageBus messageBus,
            ITestFrameworkDiscoveryOptions discoveryOptions) 
        {
            throw new System.NotImplementedException();
        }
    }
}