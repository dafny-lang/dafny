using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.VisualStudio.TestPlatform.ObjectModel;
using Microsoft.VisualStudio.TestPlatform.ObjectModel.Client;
using Microsoft.VisualStudio.TestPlatform.ObjectModel.Logging;

namespace Microsoft.Dafny {
  public class CSVTestLogger : ITestLoggerWithParameters {

    private readonly List<TestResult> results = new();

    public void Initialize(TestLoggerEvents events, string testRunDirectory) {
    }

    public void Initialize(TestLoggerEvents events, Dictionary<string, string> parameters) {
      events.TestResult += TestResultHandler;
      events.TestRunComplete += TestRunCompleteHandler;
    }

    private void TestResultHandler(object sender, TestResultEventArgs e) {
      results.Add(e.Result);
    }

    private int? GetResourceCount(TestResult result) {
      return result.GetPropertyValue<int?>(BoogieXmlConvertor.ResourceCountProperty, null);
    }

    private void TestRunCompleteHandler(object sender, TestRunCompleteEventArgs e) {
      foreach (var result in results.OrderByDescending(GetResourceCount)) {
        Console.Out.WriteLine($"{result.TestCase.DisplayName}, {result.Outcome}, {result.Duration}");
      }
    }
  }
}
