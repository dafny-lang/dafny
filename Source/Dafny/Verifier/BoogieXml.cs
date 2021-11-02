using System;
using System.Collections.Generic;
using System.Linq;
using System.Xml;
using System.Xml.Linq;
using Microsoft.Boogie;
using Microsoft.VisualStudio.TestPlatform.Extensions.TrxLogger;
using Microsoft.VisualStudio.TestPlatform.ObjectModel;
using Microsoft.VisualStudio.TestPlatform.ObjectModel.Client;
using Microsoft.VisualStudio.TestPlatform.ObjectModel.Logging;

namespace Microsoft.Dafny {
  public static class BoogieXml {

    public static void RaiseTestLoggerEvents(string fileName, string loggerConfig) {
      // The only supported value for now
      if (loggerConfig != "trx") {
        throw new ArgumentException($"Unsupported verification logger config: {loggerConfig}");
      }
      
      var events = new LocalTestLoggerEvents();
      var logger = new TrxLogger();
      logger.Initialize(events, new Dictionary<string, string> {
        ["TestRunDirectory"] = Constants.DefaultResultsDirectory
      });
      events.EnableEvents();

      string currentFileFragment = null;
      XElement root = XElement.Load(fileName);
      var testResults = new List<TestResult>();
      foreach(var child in root.Nodes().OfType<XElement>()) {
        if (child.Name.LocalName == "fileFragment") {
          currentFileFragment = child.Attribute("name")!.Value;
        } else if (child.Name.LocalName == "method") {
          testResults.Add(ToTestResult(child, currentFileFragment));
        }
      }

      var sortedResults = testResults
        .OrderBy(r => r.Outcome == TestOutcome.Passed)
        .ThenByDescending(r => r.Duration);
      foreach(var result in sortedResults) {
        events.RaiseTestResult(new TestResultEventArgs(result));
      }

      events.RaiseTestRunComplete(new TestRunCompleteEventArgs(
        new TestRunStatistics(),
        false, false, null, null, new TimeSpan()
      ));
    }

    private static TestResult ToTestResult(XElement node, string currentFileFragment) {
      var name = node.Attribute("name")!.Value;
      var startTime = node.Attribute("startTime")!.Value;
      var conclusionNode = node.Nodes().OfType<XElement>().Single(n => n.Name.LocalName == "conclusion");
      var endTime = conclusionNode.Attribute("endTime")!.Value;
      var duration = float.Parse(conclusionNode.Attribute("duration")!.Value);
      var outcome = conclusionNode.Attribute("outcome")!.Value;
          
      var testCase = new TestCase {
        FullyQualifiedName = name,
        ExecutorUri = new Uri("executor://dafny/something/something"),
        Source = currentFileFragment
      };

      var testResult = new TestResult(testCase) {
        StartTime = DateTimeOffset.Parse(startTime),
        EndTime = DateTimeOffset.Parse(endTime),
        Duration = TimeSpan.FromMilliseconds((long)(duration * 1000))
      };

      if (outcome == "correct") {
        testResult.Outcome = TestOutcome.Passed;
      } else {
        testResult.Outcome = TestOutcome.Failed;
        testResult.ErrorMessage = outcome;
      }

      return testResult;
    }
  }
}