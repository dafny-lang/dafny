using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Text.RegularExpressions;
using System.Threading;
using Microsoft.Boogie;

namespace Microsoft.Dafny {
  public class ProfilingOutputPrinter : OutputPrinter {
    private readonly OutputPrinter wrapped;
    private readonly Dictionary<string, decimal?> verificationTimes = new();
    private string currentlyVerifying = null;
    
    public ProfilingOutputPrinter(OutputPrinter wrapped) {
      if (!DafnyOptions.O.Trace) {
        throw new ThreadStateException("Profiling requires the /trace option");
      }
      this.wrapped = wrapped;
    }

    public Dictionary<string, decimal?> GetVerificationTimes() {
      return new Dictionary<string, decimal?>(verificationTimes);
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
      foreach (Match match in Regex.Matches(s, pattern)){
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
      foreach (Match match in Regex.Matches(s, resultPattern)){
        var groups = match.Groups;
        var result = groups["Result"].ToString();
        var time = decimal.Parse(groups["Time"].ToString());
        var vcCount = int.Parse(groups["VCCount"].ToString());
        if (currentlyVerifying != null) {
          if (result == "timed out") {
            verificationTimes.Add(currentlyVerifying, -1);
          } else if (DafnyOptions.O.TimeLimit > 0 && time > DafnyOptions.O.TimeLimit) {
            verificationTimes.Add(currentlyVerifying, -1);
          } else {
            verificationTimes.Add(currentlyVerifying, time);
          }

          currentlyVerifying = null;
        }
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

    public void PrintProfilingSummaryToConsole() {
      foreach(var pair in verificationTimes.OrderByDescending(pair => pair.Value)) {
        Console.WriteLine($"{pair.Key}: {pair.Value}");
      }
    }
    
    public void PrintProfilingSummary() {
      // var logger = new TestLogger();
      //
      // var runSettings = $@"
      // <RunSettings>
      //   <LoggerRunSettings>
      //     <Loggers>
      //       <Logger friendlyName=""trx"" enabled=""True"">
      //         <Configuration>
      //           <Verbosity>normal</Verbosity>
      //         </Configuration>
      //       </Logger>
      //     </Loggers>
      //   </LoggerRunSettings>
      // </RunSettings>
      // ";
      // var testEngine = new TestEngine();
      // var requestData = new RequestData();
      // var sources = new[] { "/Users/salkeldr/Documents/GitHub/dafny/Binaries" };
      // var discoveryCriteria = new DiscoveryCriteria(sources, 1000, runSettings);
      // testEngine.GetDiscoveryManager(requestData, null, discoveryCriteria);
      // var loggerManager = testEngine.GetLoggerManager(new RequestData());
      // loggerManager.Initialize(runSettings);
      //
      // List<TestResult> testResults = new();
      // foreach (var pair in verificationTimes.OrderByDescending(pair => pair.Value)) {
      //   var testCase = new TestCase();
      //   testCase.DisplayName = pair.Key;
      //   var result = new TestResult(testCase);
      //   result.Duration = new TimeSpan((int)(pair.Value * 1000));
      //   testResults.Add(result);
      // }
      //
      // var statsChange = new TestRunChangedEventArgs(new TestRunStatistics(), testResults, Array.Empty<TestCase>());
      // loggerManager.HandleTestRunStatsChange(statsChange);
    }
  }
}