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
      string loggerName;
      Dictionary<string, string> parameters;
      int semiColonIndex = loggerConfig.IndexOf(";");
      if (semiColonIndex >= 0) {
        loggerName = loggerConfig[..semiColonIndex];
        var parametersList = loggerConfig[(semiColonIndex + 1)..];
        parameters = parametersList.Split(",").Select(s => {
          var equalsIndex = s.IndexOf("=");
          return (s[..equalsIndex], s[(equalsIndex + 1)..]);
        }).ToDictionary(p => p.Item1, p => p.Item2);
      } else {
        loggerName = loggerConfig;
        parameters = new();
      }

      // The only supported value for now
      if (loggerName != "trx") {
        throw new ArgumentException($"Unsupported verification logger name: {loggerName}");
      }

      // Provide just enough configuration for the TRX logger to work
      parameters["TestRunDirectory"] = Constants.DefaultResultsDirectory;

      var events = new LocalTestLoggerEvents();
      var logger = new TrxLogger();
      logger.Initialize(events, parameters);
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
      var childSplits = method.Nodes().OfType<XElement>().Where(child => child.Name.LocalName == "split").ToList();
      return childSplits.Count > 1
        ? childSplits.Select(childSplit => TestResultForSplit(currentFileFragment, method, childSplit))
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
      var outcome = conclusionNode.Attribute("outcome")!.Value;

      var testCase = TestCaseForEntry(currentFileFragment, name);
      var testResult = new TestResult(testCase) {
        StartTime = DateTimeOffset.Parse(startTime),
        Duration = TimeSpan.FromMilliseconds((long)(duration * 1000)),
        EndTime = DateTimeOffset.Parse(endTime)
      };

      if (outcome == "correct") {
        testResult.Outcome = TestOutcome.Passed;
      } else {
        testResult.Outcome = TestOutcome.Failed;
        testResult.ErrorMessage = outcome;
      }

      return testResult;
    }

    private static TestResult TestResultForSplit(string currentFileFragment, XElement methodNode, XElement splitNode) {
      var methodName = methodNode.Attribute("name")!.Value;
      var splitNumber = splitNode.Attribute("number")!.Value;
      var name = $"{methodName}$${splitNumber}";

      var startTime = splitNode.Attribute("startTime")!.Value;
      var conclusionNode = splitNode.Nodes()
                                            .OfType<XElement>()
                                            .Single(n => n.Name.LocalName == "conclusion");
      var duration = float.Parse(conclusionNode.Attribute("duration")!.Value);
      var outcome = conclusionNode.Attribute("outcome")!.Value;

      var testCase = TestCaseForEntry(currentFileFragment, name);
      var testResult = new TestResult(testCase) {
        StartTime = DateTimeOffset.Parse(startTime),
        Duration = TimeSpan.FromMilliseconds((long)(duration * 1000))
      };

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