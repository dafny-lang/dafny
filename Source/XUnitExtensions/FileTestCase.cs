using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Threading;
using System.Threading.Tasks;
using Xunit;
using Xunit.Abstractions;
using Xunit.Sdk;

namespace XUnitExtensions {
  public class FileTestCase : LongLivedMarshalByRefObject, IXunitTestCase {

    protected XunitTestCase innerTestCase;

    public FileTestCase(IMessageSink diagnosticMessageSink, ITestMethod testMethod, IFileTheoryRowData data) {
      var collection = new TestCollection(testMethod.TestClass.TestCollection.TestAssembly,
        (ITypeInfo)null, "Test collection for " + data.TestDisplayName);
      var testClassWithCollection = new TestClass(collection, testMethod.TestClass.Class);
      var testMethodWithCollection = new TestMethod(testClassWithCollection, testMethod.Method);
      
      innerTestCase = new XunitTestCase(diagnosticMessageSink, TestMethodDisplay.Method, TestMethodDisplayOptions.All,
        testMethodWithCollection, data.GetData());
      if (data.Traits != null) {
        foreach(var (key, value) in data.Traits) {
          innerTestCase.Traits.Add(key, value);
        }
      }

      innerTestCase.SourceInformation = data.SourceInformation;
      SkipReason = data.Skip;
    }

    [Obsolete("Called by the de-serializer", error: true)]
    public FileTestCase() { }

    public void Deserialize(IXunitSerializationInfo info) {
      innerTestCase = info.GetValue<XunitTestCase>(nameof(innerTestCase));
      SkipReason = info.GetValue<string>(nameof(SkipReason));
    }

    public void Serialize(IXunitSerializationInfo info) {
      info.AddValue(nameof(innerTestCase), innerTestCase);
      info.AddValue(nameof(SkipReason), SkipReason);
    }
    public string SkipReason { get; protected set; }

    public ISourceInformation SourceInformation {
      get => innerTestCase.SourceInformation;
      set => innerTestCase.SourceInformation = value;
    }

    public string DisplayName => innerTestCase.DisplayName;
    public ITestMethod TestMethod => innerTestCase.TestMethod;
    public object[] TestMethodArguments => innerTestCase.TestMethodArguments;
    public Dictionary<string, List<string>> Traits => innerTestCase.Traits;
    public string UniqueID => innerTestCase.UniqueID;
    public Exception InitializationException => innerTestCase.InitializationException;
    public IMethodInfo Method => innerTestCase.Method;
    public int Timeout => innerTestCase.Timeout;
    
    public Task<RunSummary> RunAsync(IMessageSink diagnosticMessageSink, IMessageBus messageBus, object[] constructorArguments,
      ExceptionAggregator aggregator, CancellationTokenSource cancellationTokenSource) {

      return new XunitTestCaseRunner(
        this,
        DisplayName,
        SkipReason,
        constructorArguments,
        TestMethodArguments,
        messageBus,
        aggregator,
        cancellationTokenSource
      ).RunAsync();
    }
  }
}