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
using Microsoft.Boogie;
using Microsoft.VisualStudio.TestPlatform.Extensions.TrxLogger;
using Microsoft.VisualStudio.TestPlatform.ObjectModel;
using Microsoft.VisualStudio.TestPlatform.ObjectModel.Client;
using Microsoft.VisualStudio.TestPlatform.ObjectModel.Logging;

namespace Microsoft.Dafny {

  /// <summary>
  /// Utility to translate verification results into logs in several formats:
  ///  * TRX files, which can be understood and visualized by various .NET tools.
  ///  * CSV files, which are easier to parse and summarize. 
  ///  * human-readable text output.
  /// </summary>
  public static class VerificationResultLogger {

    public static TestProperty ResourceCountProperty = TestProperty.Register("TestResult.ResourceCount", "TestResult.ResourceCount", typeof(int), typeof(TestResult));

    public static void RaiseTestLoggerEvents(DafnyOptions options, ProofDependencyManager depManager) {
      var loggerConfigs = options.VerificationLoggerConfigs;
      // Provide just enough configuration for the loggers to work
      var parameters = new Dictionary<string, string> {
        ["TestRunDirectory"] = Constants.DefaultResultsDirectory
      };

      var events = new LocalTestLoggerEvents();
      var verificationResults = (options.Printer as DafnyConsolePrinter).VerificationResults.ToList();
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
        } else if (loggerName == "text") {
          // This logger doesn't implement the ITestLogger interface because
          // it uses information that's tricky to encode in a TestResult.
          var textLogger = new TextLogger(depManager, options.OutputWriter);
          textLogger.Initialize(parameters);
          textLogger.LogResults(verificationResults);
          return;
        } else {
          throw new ArgumentException($"unsupported verification logger config: {loggerConfig}");
        }
      }
      events.EnableEvents();

      // Sort failures to the top, and then slower procedures first.
      // Loggers may not maintain this ordering unfortunately.
      var results = VerificationToTestResults(verificationResults.Select(e => (e.Implementation, e.Result.VCResults)))
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

    private static IEnumerable<TestResult> VerificationToTestResults(IEnumerable<(DafnyConsolePrinter.ImplementationLogEntry, List<DafnyConsolePrinter.VCResultLogEntry>)> verificationResults) {
      var testResults = new List<TestResult>();

      foreach (var ((verbName, currentFile), vcResults) in verificationResults) {
        foreach (var vcResult in vcResults.OrderBy(r => r.VCNum)) {
          var name = vcResults.Count() > 1
            ? verbName + $" (assertion batch {vcResult.VCNum})"
            : verbName;
          var testCase = new TestCase {
            FullyQualifiedName = name,
            ExecutorUri = new Uri("executor://dafnyverifier/v1"),
            Source = ((IToken)currentFile).Uri.LocalPath
          };
          var testResult = new TestResult(testCase) {
            StartTime = vcResult.StartTime,
            Duration = vcResult.RunTime
          };
          testResult.SetPropertyValue(ResourceCountProperty, vcResult.ResourceCount);
          if (vcResult.Outcome == ProverInterface.Outcome.Valid) {
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
