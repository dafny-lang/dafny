//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------
using System;
using System.Collections.Generic;
using System.IO;
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
  /// as test results through common loggers on the .NET platform. For now we support two formats:
  ///  * TRX files, which can be understood and visualized by various .NET tools.
  ///  * CSV files, which are easier to parse and summarize. 
  /// </summary>
  public static class BoogieXmlConvertor {

    public static TestProperty ResourceCountProperty = TestProperty.Register("TestResult.ResourceCount", "TestResult.ResourceCount", typeof(int), typeof(TestResult));

    public static void RaiseTestLoggerEvents(string fileName, List<string> loggerConfigs) {
      // Provide just enough configuration for the loggers to work
      var parameters = new Dictionary<string, string> {
        ["TestRunDirectory"] = Constants.DefaultResultsDirectory
      };

      var events = new LocalTestLoggerEvents();
      foreach (var loggerConfig in loggerConfigs) {
        string loggerName;
        int semiColonIndex = loggerConfig.IndexOf(";");
        if (semiColonIndex >= 0) {
          loggerName = loggerConfig[..semiColonIndex];
          var parametersList = loggerConfig[(semiColonIndex + 1)..];
          foreach (string s in parametersList.Split(",")) {
            var equalsIndex = s.IndexOf("=");
            parameters.Add(s[..equalsIndex], s[(equalsIndex + 1)..]);
          }
        } else {
          loggerName = loggerConfig;
        }

        if (loggerName == "trx") {
          var logger = new TrxLogger();
          logger.Initialize(events, parameters);
        } else if (loggerName == "csv") {
          var csvLogger = new CSVTestLogger();
          csvLogger.Initialize(events, parameters);
        } else if (loggerName == "text") {
          // This doesn't actually use the XML converter. It instead uses a collection of VerificationResult
          // objects. Ultimately, the other loggers should be converted to use those objects, as well,
          // and then it would make sense to rename this class.
          var textLogger = new TextLogger();
          textLogger.Initialize(parameters);
          textLogger.LogResults((DafnyOptions.O.Printer as DafnyConsolePrinter).VerificationResults);
        } else {
          throw new ArgumentException("Unsupported verification logger config: {loggerConfig}");
        }
      }
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
            testResults.AddRange(TestResultsForMethod(child, currentFileFragment));
            break;
        }
      }

      return testResults;
    }

    private static IEnumerable<TestResult> TestResultsForMethod(XElement method, string currentFileFragment) {
      // Only report the top level method result if there was no splitting
      var childBatches = method.Nodes().OfType<XElement>().Where(child => child.Name.LocalName == "assertionBatch").ToList();
      return childBatches.Count > 1
        ? childBatches.Select(childBatch => TestResultForBatch(currentFileFragment, method, childBatch))
        : new[] { TestResultForMethod(currentFileFragment, method) };
    }

    private static TestResult TestResultForMethod(string currentFileFragment, XElement node) {
      var name = node.Attribute("name")!.Value;
      var startTime = node.Attribute("startTime")!.Value;
      var conclusionNode = node.Nodes()
                                       .OfType<XElement>()
                                       .Single(n => n.Name.LocalName == "conclusion");
      var endTime = conclusionNode.Attribute("endTime")!.Value;
      var duration = float.Parse(conclusionNode.Attribute("duration")!.Value);
      var resourceCount = conclusionNode.Attribute("resourceCount")?.Value;
      var outcome = conclusionNode.Attribute("outcome")!.Value;

      var testCase = TestCaseForEntry(currentFileFragment, name);
      var testResult = new TestResult(testCase) {
        StartTime = DateTimeOffset.Parse(startTime),
        Duration = TimeSpan.FromMilliseconds((long)(duration * 1000)),
        EndTime = DateTimeOffset.Parse(endTime)
      };

      if (resourceCount != null) {
        testResult.SetPropertyValue(ResourceCountProperty, int.Parse(resourceCount));
      }

      if (outcome == "correct") {
        testResult.Outcome = TestOutcome.Passed;
      } else {
        testResult.Outcome = TestOutcome.Failed;
        testResult.ErrorMessage = outcome;
      }

      return testResult;
    }

    private static TestResult TestResultForBatch(string currentFileFragment, XElement methodNode, XElement batchNode) {
      var methodName = methodNode.Attribute("name")!.Value;
      var batchNumber = batchNode.Attribute("number")!.Value;
      var name = $"{methodName}$${batchNumber}";

      var startTime = batchNode.Attribute("startTime")!.Value;
      var conclusionNode = batchNode.Nodes()
                                            .OfType<XElement>()
                                            .Single(n => n.Name.LocalName == "conclusion");
      var duration = float.Parse(conclusionNode.Attribute("duration")!.Value);
      var resourceCount = conclusionNode.Attribute("resourceCount")?.Value;
      var outcome = conclusionNode.Attribute("outcome")!.Value;

      var testCase = TestCaseForEntry(currentFileFragment, name);
      var testResult = new TestResult(testCase) {
        StartTime = DateTimeOffset.Parse(startTime),
        Duration = TimeSpan.FromMilliseconds((long)(duration * 1000))
      };

      if (resourceCount != null) {
        testResult.SetPropertyValue(ResourceCountProperty, int.Parse(resourceCount));
      }

      if (outcome == "valid") {
        testResult.Outcome = TestOutcome.Passed;
      } else {
        testResult.Outcome = TestOutcome.Failed;
        testResult.ErrorMessage = outcome;
      }

      return testResult;
    }

    private static TestCase TestCaseForEntry(string currentFileFragment, string entryName) {
      return new TestCase {
        FullyQualifiedName = entryName,
        ExecutorUri = new Uri("executor://dafnyverifier/v1"),
        Source = currentFileFragment
      };
    }
  }
}
