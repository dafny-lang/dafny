using System;
using System.Collections.Generic;
using System.Reflection;
using Xunit.Abstractions;
using Xunit.Sdk;

namespace DefaultNamespace {
    public class FanOutExecutor : XunitTestFrameworkExecutor {
        public FanOutExecutor(AssemblyName assemblyName, ISourceInformationProvider sourceInformationProvider, IMessageSink diagnosticMessageSink) 
            : base(assemblyName, sourceInformationProvider, diagnosticMessageSink) 
        {
            this.TestAssembly = new TestAssembly(this.AssemblyInfo, AppDomain.CurrentDomain.SetupInformation.ConfigurationFile, assemblyName.Version);
        }

        protected override ITestFrameworkDiscoverer CreateDiscoverer() {
            throw new System.NotImplementedException();
        }

        protected override async void RunTestCases(
            IEnumerable<IXunitTestCase> testCases,
            IMessageSink executionMessageSink,
            ITestFrameworkExecutionOptions executionOptions)
        {
            using (FanOutTestAssemblyRunner assemblyRunner = new FanOutTestAssemblyRunner(TestAssembly, testCases, DiagnosticMessageSink, executionMessageSink, executionOptions))
            {
                RunSummary runSummary = await assemblyRunner.RunAsync();
            }
        }
    }
}