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

namespace Microsoft.Dafny {

  /// <summary>
  /// Utility to translate verification results into logs in several formats:
  ///  * TRX files, which can be understood and visualized by various .NET tools.
  ///  * CSV files, which are easier to parse and summarize. 
  ///  * human-readable text output.
  /// </summary>
  public static class LegacyVerificationResultLogger {

    public static void RaiseTestLoggerEvents(DafnyOptions options, ProofDependencyManager depManager) {
      var loggerConfigs = options.Get(CommonOptionBag.VerificationLogFormat);

      var events = new LocalTestLoggerEvents();
      var verificationResults = ((DafnyConsolePrinter)options.Printer).VerificationResults.ToList();
      List<IDisposable> disposables = new();
      foreach (var loggerConfig in loggerConfigs) {
        VerificationResultLogger.ParseParametersAndLoggerName(loggerConfig, out var parameters, out var loggerName);

        if (loggerName == "trx") {
          var logger = new TrxLogger();
          logger.Initialize(events, parameters);
        } else if (loggerName == "csv") {
          var csvLogger = new CSVTestLogger(options.OutputWriter);
          csvLogger.Initialize(events, parameters);
        } else if (loggerName == "json") {
          // This logger doesn't implement the ITestLogger interface because
          // it uses information that's tricky to encode in a TestResult.
          var jsonLogger = new LegacyJsonVerificationLogger(depManager, options.OutputWriter);
          disposables.Add(jsonLogger);
          jsonLogger.Initialize(parameters);
          jsonLogger.LogResults(verificationResults);
        } else if (loggerName == "text") {
          // This logger doesn't implement the ITestLogger interface because
          // it uses information that's tricky to encode in a TestResult.
          var textLogger = new LegacyTextVerificationLogger(depManager, options.OutputWriter);
          disposables.Add(textLogger);
          textLogger.Initialize(parameters);
          textLogger.LogResults(verificationResults);
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
      foreach (var disposable in disposables) {
        disposable.Dispose();
      }
    }

    private static IEnumerable<TestResult> VerificationToTestResults(IEnumerable<(DafnyConsolePrinter.ImplementationLogEntry, List<VerificationRunResultPartialCopy>)> verificationResults) {
      var testResults = new List<TestResult>();

      foreach (var ((verbName, currentFile), vcResults) in verificationResults) {
        var scopeResult = new VerificationScopeResult(new VerificationScope(verbName, currentFile),
          vcResults.Select(LegacyJsonVerificationLogger.VCResultLogEntryToPartialVerificationRunResult).ToList());
        testResults.AddRange(VerificationResultLogger.VerificationToTestResults(scopeResult));
      }

      return testResults;
    }
  }
}
