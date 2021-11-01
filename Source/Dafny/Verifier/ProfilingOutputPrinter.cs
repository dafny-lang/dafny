using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Text.RegularExpressions;
using System.Threading;
using Microsoft.Boogie;
using Microsoft.VisualStudio.TestPlatform.Extensions.TrxLogger;
using Microsoft.VisualStudio.TestPlatform.ObjectModel;
using Microsoft.VisualStudio.TestPlatform.ObjectModel.Client;
using Microsoft.VisualStudio.TestPlatform.ObjectModel.Logging;

namespace Microsoft.Dafny {
  public class ProfilingOutputPrinter : OutputPrinter {
    private readonly OutputPrinter wrapped;
    private readonly LocalTestLoggerEvents events;
    private string currentlyVerifying = null;

    public ProfilingOutputPrinter(OutputPrinter wrapped) {
      if (!DafnyOptions.O.Trace) {
        throw new ThreadStateException("Profiling requires the /trace option");
      }
      this.wrapped = wrapped;
      events = new LocalTestLoggerEvents();
      var logger = new TrxLogger();
      logger.Initialize(events, new Dictionary<string, string> {
        ["TestRunDirectory"] = Constants.DefaultResultsDirectory
      });
      events.EnableEvents();
    }

    public void ErrorWriteLine(TextWriter tw, string s) {
      wrapped.ErrorWriteLine(tw, s);
    }

    public void ErrorWriteLine(TextWriter tw, string format, params object[] args) {
      wrapped.ErrorWriteLine(tw, format, args);
    }

    public void AdvisoryWriteLine(string format, params object[] args) {
      wrapped.AdvisoryWriteLine(format, args);
    }

    public void Inform(string s, TextWriter tw) {
      string pattern = @"^Verifying (?<TaskName>\w+)\$\$(?<CallableName>[\w\.]+) \.\.\.$";
      string resultPattern = @"^  \[(?<Time>.*) s, (?<VCCount>.*) proof obligations\]  (?<Result>[a-zA-Z ]+)$";
      foreach (Match match in Regex.Matches(s, pattern)) {
        GroupCollection groups = match.Groups;
        var callableName = groups["CallableName"].ToString();
        var taskName = groups["TaskName"].ToString();
        if (taskName == "CheckWellformed") {
          currentlyVerifying = $"{callableName} (Well-formedness check)";
        } else if (taskName == "OverrideCheck") {
          currentlyVerifying = $"{callableName} (Override check)";
        } else {
          currentlyVerifying = $"{callableName} (Implementation)";
        }
      }
      foreach (Match match in Regex.Matches(s, resultPattern)) {
        var groups = match.Groups;
        var result = groups["Result"].ToString();
        var time = decimal.Parse(groups["Time"].ToString());
        var vcCount = int.Parse(groups["VCCount"].ToString());
        if (currentlyVerifying != null) {
          var testCase = new TestCase {
            FullyQualifiedName = currentlyVerifying,
            ExecutorUri = new Uri("executor://dafny/something/something"),
            Source = "lol.dfy"
          };

          var testResult = new TestResult(testCase) {
            Duration = TimeSpan.FromMilliseconds((long)(time * 1000))
          };

          if (DafnyOptions.O.TimeLimit > 0 && time > DafnyOptions.O.TimeLimit) {
            testResult.Outcome = TestOutcome.Failed;
            testResult.ErrorMessage = "timed out";
          } else {
            testResult.Outcome = OutcomeForResult(result);
            if (testResult.Outcome != TestOutcome.Passed) {
              testResult.ErrorMessage = result;
            }
          }
          
          events.RaiseTestResult(new TestResultEventArgs(testResult));

          currentlyVerifying = null;
        }
      }
    }

    private TestOutcome OutcomeForResult(string result) {
      if (result == "verified") {
        return TestOutcome.Passed;
      } else {
        return TestOutcome.Failed;
      }
    }

    public void WriteTrailer(PipelineStatistics stats) {
      wrapped.WriteTrailer(stats);
    }

    public void WriteErrorInformation(ErrorInformation errorInfo, TextWriter tw, bool skipExecutionTrace = true) {
      wrapped.WriteErrorInformation(errorInfo, tw, skipExecutionTrace);
    }

    public void ReportBplError(IToken tok, string message, bool error, TextWriter tw, string category = null) {
      wrapped.ReportBplError(tok, message, error, tw, category);
    }

    public void Dispose() {
      events.RaiseTestRunComplete(new TestRunCompleteEventArgs(
        new TestRunStatistics(),
        false, false, null, null, new TimeSpan()
      ));
    }
  }
}