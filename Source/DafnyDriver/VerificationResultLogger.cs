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
using DafnyDriver.Commands;
using Microsoft.Boogie;
using Microsoft.VisualStudio.TestPlatform.Extensions.TrxLogger;
using Microsoft.VisualStudio.TestPlatform.ObjectModel;
using Microsoft.VisualStudio.TestPlatform.ObjectModel.Client;
using Microsoft.VisualStudio.TestPlatform.ObjectModel.Logging;
using VC;

namespace Microsoft.Dafny {
  public record VerificationScope(string Name, Boogie.IToken Token);

  /// <summary>
  /// Utility to translate verification results into logs in several formats:
  ///  * TRX files, which can be understood and visualized by various .NET tools.
  ///  * CSV files, which are easier to parse and summarize. 
  ///  * human-readable text output.
  /// </summary>
  public static class VerificationResultLogger {

    public static TestProperty ResourceCountProperty = TestProperty.Register("TestResult.ResourceCount", "TestResult.ResourceCount", typeof(int), typeof(TestResult));

    public static void RaiseTestLoggerEvents(DafnyOptions options, Dictionary<ICanVerify, CliCanVerifyState> verificationResults, ProofDependencyManager depManager) {
      var loggerConfigs = options.VerificationLoggerConfigs;
      // Provide just enough configuration for the loggers to work
      var parameters = new Dictionary<string, string> {
        ["TestRunDirectory"] = Constants.DefaultResultsDirectory
      };

      var implementationResults =
        verificationResults.Values.SelectMany(x => x.CompletedParts).
          GroupBy(v => new VerificationScope(v.Task.ScopeId, v.Task.ScopeToken), t => t.Result.Result).ToList();

      var events = new LocalTestLoggerEvents();
      foreach (var loggerConfig in loggerConfigs) {
        string loggerName;
        int semiColonIndex = loggerConfig.IndexOf(";");
        if (semiColonIndex >= 0) {
          loggerName = loggerConfig[..semiColonIndex];
          var parametersList = loggerConfig[(semiColonIndex + 1)..];
          foreach (string s in parametersList.Split(",")) {
            var equalsIndex = s.IndexOf("=");
            if (equalsIndex >= 0) {
              parameters.Add(s[..equalsIndex], s[(equalsIndex + 1)..]);
            } else {
              throw new ArgumentException($"unknown parameter to `/verificationLogger:csv`: {s}");
            }
          }
        } else {
          loggerName = loggerConfig;
        }

        if (loggerName == "trx") {
          var logger = new TrxLogger();
          logger.Initialize(events, parameters);
        } else if (loggerName == "csv") {
          var csvLogger = new CSVTestLogger(options.OutputWriter);
          csvLogger.Initialize(events, parameters);
        } else if (loggerName == "json") {
          // This logger doesn't implement the ITestLogger interface because
          // it uses information that's tricky to encode in a TestResult.
          var jsonLogger = new JsonVerificationLogger(depManager, options.OutputWriter);
          jsonLogger.Initialize(parameters);
          jsonLogger.LogResults(implementationResults);
        } else if (loggerName == "text") {
          // This logger doesn't implement the ITestLogger interface because
          // it uses information that's tricky to encode in a TestResult.
          var textLogger = new TextVerificationLogger(depManager, options.OutputWriter);
          textLogger.Initialize(parameters);
          textLogger.LogResults(implementationResults);
        } else {
          throw new ArgumentException($"unsupported verification logger config: {loggerConfig}");
        }
      }
      events.EnableEvents();

      // Sort failures to the top, and then slower procedures first.
      // Loggers may not maintain this ordering unfortunately.
      var results = VerificationToTestResults(implementationResults)
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

    private static IEnumerable<TestResult> VerificationToTestResults(List<IGrouping<VerificationScope, VerificationRunResult>> verificationResults) {
      var testResults = new List<TestResult>();

      foreach (var group in verificationResults) {
        var vcResults = group;
        var verificationScope = group.Key;
        foreach (var vcResult in vcResults.OrderBy(r => r.VcNum)) {
          var name = vcResults.Count() > 1
            ? verificationScope.Name + $" (assertion batch {vcResult.VcNum})"
            : verificationScope.Name;
          var testCase = new TestCase {
            FullyQualifiedName = name,
            ExecutorUri = new Uri("executor://dafnyverifier/v1"),
            Source = ((IToken)verificationScope.Token).Uri.LocalPath
          };
          var testResult = new TestResult(testCase) {
            StartTime = vcResult.StartTime,
            Duration = vcResult.RunTime
          };
          testResult.SetPropertyValue(ResourceCountProperty, vcResult.ResourceCount);
          if (vcResult.Outcome == SolverOutcome.Valid) {
            testResult.Outcome = TestOutcome.Passed;
          } else {
            testResult.Outcome = TestOutcome.Failed;
            testResult.ErrorMessage = vcResult.Outcome.ToString();
          }
          testResults.Add(testResult);
        }
      }

      return testResults;
    }
  }
}
