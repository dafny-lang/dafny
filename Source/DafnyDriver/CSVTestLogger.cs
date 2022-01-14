using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using Microsoft.VisualStudio.TestPlatform.ObjectModel;
using Microsoft.VisualStudio.TestPlatform.ObjectModel.Client;
using Microsoft.VisualStudio.TestPlatform.ObjectModel.Logging;

namespace Microsoft.Dafny {
  public class CSVTestLogger : ITestLoggerWithParameters {

    private readonly List<TestResult> results = new();
    private TextWriter writer = null;

    public void Initialize(TestLoggerEvents events, string testRunDirectory) {
    }

    public void Initialize(TestLoggerEvents events, Dictionary<string, string> parameters) {
      events.TestResult += TestResultHandler;
      events.TestRunComplete += TestRunCompleteHandler;
      if (parameters.TryGetValue("LogFileName", out string filename)) {
        writer = new StreamWriter(filename);
      }
    }

    private void TestResultHandler(object sender, TestResultEventArgs e) {
      results.Add(e.Result);
    }

    private void TestRunCompleteHandler(object sender, TestRunCompleteEventArgs e) {
      var realWriter = writer ?? Console.Out;
      foreach (var result in results.OrderByDescending(r => r.Duration)) {
        realWriter.WriteLine($"{result.TestCase.DisplayName}, {result.Outcome}, {result.Duration}");
      }
      writer?.Close();
    }
  }
}
