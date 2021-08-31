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

    public FileTestCase(IMessageSink diagnosticMessageSink, string path, ITestMethod testMethod, ITheoryRowData data) {
      innerTestCase = new XunitTestCase(diagnosticMessageSink, TestMethodDisplay.Method, testMethod, data.GetData());
      foreach (var (key, value) in data.Traits) {
        innerTestCase.Traits.Add(key, value);
      }
      innerTestCase.SourceInformation = new SourceInformation { FileName = path };
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
    public string DisplayName => innerTestCase.DisplayName;
    public string SkipReason {
      get;
      protected set;
    }

    public ISourceInformation SourceInformation {
      get => innerTestCase.SourceInformation;
      set => innerTestCase.SourceInformation = value;
    }

    public ITestMethod TestMethod => innerTestCase.TestMethod;
    public object[] TestMethodArguments => innerTestCase.TestMethodArguments;
    public Dictionary<string, List<string>> Traits => innerTestCase.Traits;
    public string UniqueID => innerTestCase.UniqueID;

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

    public Exception InitializationException => innerTestCase.InitializationException;
    public IMethodInfo Method => innerTestCase.Method;
    public int Timeout => innerTestCase.Timeout;
  }
}