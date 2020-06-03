using System;
using System.Collections.Generic;
using System.ComponentModel.Design;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using Xunit.Abstractions;
using Xunit.Sdk;

namespace DefaultNamespace {
    public class FanOutTestAssemblyRunner : TestAssemblyRunner<IXunitTestCase> {
        public FanOutTestAssemblyRunner(ITestAssembly testAssembly,
            IEnumerable<IXunitTestCase> testCases,
            IMessageSink diagnosticMessageSink,
            IMessageSink executionMessageSink,
            ITestFrameworkExecutionOptions executionOptions)
            : base(testAssembly, testCases, diagnosticMessageSink, executionMessageSink, executionOptions) {
        }

        protected override string GetTestFrameworkDisplayName() {
            return "Fan-Out Framework";
        }

        protected override Task<RunSummary> RunTestCollectionAsync(IMessageBus messageBus,
            ITestCollection testCollection, IEnumerable<IXunitTestCase> testCases,
            CancellationTokenSource cancellationTokenSource) {
            return new XunitTestCollectionRunner(testCollection, testCases, this.DiagnosticMessageSink, messageBus,
                this.TestCaseOrderer, new ExceptionAggregator(this.Aggregator), cancellationTokenSource).RunAsync();
        }
    }
}