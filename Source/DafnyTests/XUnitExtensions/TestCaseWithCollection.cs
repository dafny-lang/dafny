using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Threading;
using System.Threading.Tasks;
using Xunit;
using Xunit.Abstractions;
using Xunit.Sdk;

namespace XUnitExtensions {
  public class TestCaseWithCollection : LongLivedMarshalByRefObject, IXunitTestCase {
        
    private IXunitTestCase testCase;
    private ITestMethod testMethod;

    public TestCaseWithCollection(IXunitTestCase testCase, ITestCollection collection)
    {
      this.testCase = testCase;
            
      var testClassWithCollection = new TestClass(collection, testCase.TestMethod.TestClass.Class);
      this.testMethod = new TestMethod(testClassWithCollection, testCase.TestMethod.Method);
    }
        
    [Obsolete("Called by the de-serializer", error: true)]
    public TestCaseWithCollection() { }
        
    public void Deserialize(IXunitSerializationInfo info) {
      testCase = info.GetValue<IXunitTestCase>("InnerTestCase");
      testMethod = info.GetValue<ITestMethod>("TestMethod");
    }

    public void Serialize(IXunitSerializationInfo info) {
      info.AddValue("InnerTestCase", testCase);
      info.AddValue("TestMethod", testMethod);
    }
    public string DisplayName { get { return testCase.DisplayName; } }
    public string SkipReason { get { return testCase.SkipReason; } }
    public ISourceInformation SourceInformation
    {
      get { return testCase.SourceInformation; }
      set { testCase.SourceInformation = value; }
    }
    public ITestMethod TestMethod { get { return testMethod; } }

    public object[] TestMethodArguments { get { return testCase.TestMethodArguments; } }
    public Dictionary<string, List<string>> Traits { get { return testCase.Traits; } }
    public string UniqueID { get { return testCase.UniqueID; } }

    public Task<RunSummary> RunAsync(IMessageSink diagnosticMessageSink, IMessageBus messageBus, object[] constructorArguments,
      ExceptionAggregator aggregator, CancellationTokenSource cancellationTokenSource) {
      return testCase.RunAsync(diagnosticMessageSink, messageBus, constructorArguments, aggregator, cancellationTokenSource);
    }

    public Exception InitializationException { get; }
    public IMethodInfo Method { get; }
    public int Timeout { get; }
  }
}