//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------
using System;
using System.Collections.Generic;
using System.Linq;
using System.Xml.Linq;
using Microsoft.VisualStudio.TestPlatform.Extensions.TrxLogger;
using Microsoft.VisualStudio.TestPlatform.ObjectModel;
using Microsoft.VisualStudio.TestPlatform.ObjectModel.Client;
using Microsoft.VisualStudio.TestPlatform.ObjectModel.Logging;

namespace Microsoft.Dafny {

  /// <summary>
  /// Utility to parse the XML format produced by Boogie's /xml option and emit the
  /// results therein as test logger events, allowing us to deliver verification results
  /// as test results through common loggers on the .NET platform. For now we are just supporting
  /// outputting TRX files, which can be understood and visualized by various tools.
  /// </summary>
  public static class BoogieXmlConvertor {

    public static void RaiseTestLoggerEvents(string fileName, string loggerConfig) {
      // The only supported value for now
      if (loggerConfig != "trx") {
        throw new ArgumentException($"Unsupported verification logger config: {loggerConfig}");
      }

      var events = new LocalTestLoggerEvents();
      var logger = new TrxLogger();
      // Provide just enough configuration for the TRX logger to work
      logger.Initialize(events, new Dictionary<string, string> {
        ["TestRunDirectory"] = Constants.DefaultResultsDirectory
      });
      events.EnableEvents();

      // Sort failures to the top, and then slower procedures first.
      // Loggers may not maintain this ordering unfortunately.
      var results = ReadTestResults(fileName)
        .OrderBy(r => r.Outcome == TestOutcome.Passed)
        .ThenByDescending(r => r.Duration);
      foreach (var result in results) {
        events.RaiseTestResult(new TestResultEventArgs(result));
      }

      events.RaiseTestRunComplete(new TestRunCompleteEventArgs(
        new TestRunStatistics(),
        false, false, null, null, new TimeSpan()
      ));
    }

    public static IEnumerable<TestResult> ReadTestResults(string xmlFileName) {
      string currentFileFragment = null;
      var root = XElement.Load(xmlFileName);
      var testResults = new List<TestResult>();
      foreach (var child in root.Nodes().OfType<XElement>()) {
        switch (child.Name.LocalName) {
          case "fileFragment":
            currentFileFragment = child.Attribute("name")!.Value;
            break;
          case "method":
            testResults.Add(ToTestResult(child, currentFileFragment));
            break;
        }
      }

      return testResults;
    }

    private static TestResult ToTestResult(XElement node, string currentFileFragment) {
      var name = node.Attribute("name")!.Value;
      var startTime = node.Attribute("startTime")!.Value;
      var conclusionNode = node.Nodes()
                                       .OfType<XElement>()
                                       .Single(n => n.Name.LocalName == "conclusion");
      var endTime = conclusionNode.Attribute("endTime")!.Value;
      var duration = float.Parse(conclusionNode.Attribute("duration")!.Value);
      var outcome = conclusionNode.Attribute("outcome")!.Value;

      var testCase = new TestCase {
        FullyQualifiedName = name,
        ExecutorUri = new Uri("executor://dafnyverifier/v1"),
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