using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Text.RegularExpressions;
using Microsoft.Boogie;

namespace Microsoft.Dafny {
  public class ProfilingOutputPrinter : OutputPrinter {
    private readonly OutputPrinter wrapped;
    private readonly Dictionary<string, long?> verificationTimes = new();
    private string currentlyVerifying = null;
    private Stopwatch sw = new();
    
    public ProfilingOutputPrinter(OutputPrinter wrapped) {
      this.wrapped = wrapped;
    }

    public Dictionary<string, long?> GetVerificationTimes() {
      return new Dictionary<string, long?>(verificationTimes);
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
      wrapped.Inform(s, tw);
      
      string pattern = @"^Verifying (?<TaskName>\w+)\$\$(?<CallableName>[\w\.]+) \.\.\.$";
      string resultPattern = @"^(?<Result>[a-zA-Z ]+)$";
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
        sw.Start();
      }
      foreach (Match match in Regex.Matches(s, resultPattern)){
        GroupCollection groups = match.Groups;
        string result = groups["Result"].ToString();
        if (currentlyVerifying != null) {
          if (sw.IsRunning) {
            sw.Stop();
          }

          if (result == "timed out") {
            verificationTimes.Add(currentlyVerifying, -1);
          } else if (DafnyOptions.O.TimeLimit > 0 && sw.ElapsedMilliseconds > DafnyOptions.O.TimeLimit * 1000) {
            verificationTimes.Add(currentlyVerifying, -1);
          } else {
            verificationTimes.Add(currentlyVerifying, sw.ElapsedMilliseconds);
          }

          currentlyVerifying = null;
        }

        sw.Reset();
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

    public void PrintProfilingSummary() {
      foreach (var pair in verificationTimes.OrderByDescending(pair => pair.Value)) {
        Console.WriteLine($"{pair.Key}: {pair.Value}");
      }
    }
  }
}