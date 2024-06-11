using System;
using System.Collections.Generic;
using System.Threading;
using System.Threading.Tasks;
using Xunit;
using Xunit.Abstractions;
using Xunit.Sdk;
using SkipException = Xunit.SkipException;

namespace XUnitExtensions {
  public class FileTestCase : LongLivedMarshalByRefObject, IXunitTestCase {
    // This could use SkippableFactDiscoverer.GetSkippableExceptionNames(IAttributeInfo)
    // but it doesn't seem to be worth the complexity here yet.
    private static readonly string[] skippingExceptionNames = { typeof(SkipException).FullName! };

    // Only nullable for the sake of the deserialization constructor
    private XunitTestCase? innerTestCase;

    public string? DisplayName { get; protected set; }
    public string? SkipReason { get; protected set; }

    public FileTestCase(IMessageSink diagnosticMessageSink, ITestMethod testMethod, IFileTheoryRowData rowData) {
      var collection = new TestCollection(testMethod.TestClass.TestCollection.TestAssembly,
        testMethod.TestClass.Class, "Test collection for " + rowData.TestDisplayName);
      var testClassWithCollection = new TestClass(collection, testMethod.TestClass.Class);
      var testMethodWithCollection = new TestMethod(testClassWithCollection, testMethod.Method);

      // This unsafe cast is necessary because the signature of the constructor we're passing arguments to
      // is wrong: the type should be object?[] because arbitrary test method arguments can absolutely be null!
      object[] data = (object[])rowData.GetData();
      innerTestCase = new SkippableFactTestCase(skippingExceptionNames, diagnosticMessageSink, TestMethodDisplay.Method, TestMethodDisplayOptions.All,
        testMethodWithCollection, data);
      if (rowData.Traits != null) {
        foreach (var (key, value) in rowData.Traits) {
          innerTestCase.Traits.Add(key, value);
        }
      }

      innerTestCase.SourceInformation = rowData.SourceInformation;
      DisplayName = rowData.TestDisplayName;
      SkipReason = rowData.Skip;
    }

    [Obsolete("Called by the de-serializer", error: true)]
    public FileTestCase() { }

    public void Deserialize(IXunitSerializationInfo info) {
      innerTestCase = info.GetValue<XunitTestCase>(nameof(innerTestCase));
      DisplayName = info.GetValue<string>(nameof(DisplayName));
      SkipReason = info.GetValue<string>(nameof(SkipReason));
    }

    public void Serialize(IXunitSerializationInfo info) {
      info.AddValue(nameof(innerTestCase), innerTestCase);
      info.AddValue(nameof(DisplayName), DisplayName);
      info.AddValue(nameof(SkipReason), SkipReason);
    }

    public ISourceInformation SourceInformation {
      get => innerTestCase!.SourceInformation;
      set => innerTestCase!.SourceInformation = value;
    }

    public ITestMethod TestMethod => innerTestCase!.TestMethod;
    public object[] TestMethodArguments => innerTestCase!.TestMethodArguments;
    public Dictionary<string, List<string>> Traits => innerTestCase!.Traits;
    public string UniqueID => innerTestCase!.UniqueID;
    public Exception InitializationException => innerTestCase!.InitializationException;
    public IMethodInfo Method => innerTestCase!.Method;
    public int Timeout => innerTestCase!.Timeout;

    public async Task<RunSummary> RunAsync(IMessageSink diagnosticMessageSink, IMessageBus messageBus, object[] constructorArguments,
      ExceptionAggregator aggregator, CancellationTokenSource cancellationTokenSource) {

      // This is the same thing SkippableFactTestCase.RunAsync does.
      // support for dynamic test skipping is much cleaner in xUnit 3.
      var messageBusInterceptor = new SkippableTestMessageBus(messageBus, skippingExceptionNames);
      RunSummary result = await new XunitTestCaseRunner(
        this,
        DisplayName,
        SkipReason,
        constructorArguments,
        TestMethodArguments,
        messageBusInterceptor,
        aggregator,
        cancellationTokenSource
      ).RunAsync();
      result.Failed -= messageBusInterceptor.SkippedCount;
      result.Skipped += messageBusInterceptor.SkippedCount;
      return result;
    }
  }
}
