using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using Microsoft.VisualStudio.TestPlatform.ObjectModel;
using Microsoft.VisualStudio.TestPlatform.ObjectModel.Client;
using Microsoft.VisualStudio.TestPlatform.ObjectModel.Logging;

namespace Microsoft.Dafny {
  public class CSVTestLogger : ITestLoggerWithParameters {

    private readonly ConcurrentBag<TestResult> results = [];
    private TextWriter writer;
    private readonly IDafnyOutputWriter logWriter;
    private string writerFilename;

    public CSVTestLogger(IDafnyOutputWriter logWriter) {
      this.logWriter = logWriter;
    }

    public void Initialize(TestLoggerEvents events, string testRunDirectory) {
    }

    public void Initialize(TestLoggerEvents events, Dictionary<string, string> parameters) {
      events.TestResult += TestResultHandler;
      events.TestRunComplete += TestRunCompleteHandler;

      if (parameters.TryGetValue("LogFileName", out string filename)) {
        writer = new StreamWriter(filename);
        writerFilename = filename;
      } else {
        // Auto-generate a file name if none is specified. This uses a
        // similar approach to the TRX logger, but with simpler logic.
        const string resultsDir = "TestResults";
        Directory.CreateDirectory(resultsDir); // No-op if the directory already exists
        var dateTime = DateTime.Now.ToString("yyyy-MM-dd_HH_mm_ss");

        // Iterate through possible file names to ensure uniqueness, failing after
        // 65k tries (as in the TRX case).
        string autoFilename;
        ushort suffixCounter = 0;
        while (true) {
          if (suffixCounter == ushort.MaxValue) {
            throw new FileNotFoundException("Could not create unique file name for CSV test log.");
          }

          autoFilename =
            Path.ChangeExtension(Path.Combine(resultsDir, dateTime + "-" + suffixCounter.ToString()), ".csv");
          suffixCounter++;
          try {
            // Creating the file reserves it for use. It'll be closed here and re-opened below.
            using (var fs = File.Open(autoFilename, FileMode.CreateNew)) {
            }

            break;
          } catch (IOException) {
            // If creating the file using CreateNew failed, try again with the incremented suffix.
            continue;
          }
        }

        writer = new StreamWriter(autoFilename);
        writerFilename = autoFilename;
      }
    }

    private void TestResultHandler(object sender, TestResultEventArgs e) {
      results.Add(e.Result);
    }

    private void TestRunCompleteHandler(object sender, TestRunCompleteEventArgs e) {
      writer.WriteLine("TestResult.DisplayName,TestResult.Outcome,TestResult.Duration,TestResult.ResourceCount,RandomSeed");
      foreach (var result in results.OrderByDescending(r => r.Duration)) {
        var resourceCount = result.GetPropertyValue(VerificationResultLogger.ResourceCountProperty);
        var randomSeed = result.GetPropertyValue(VerificationResultLogger.RandomSeedProperty) ?? "unknown";
        writer.WriteLine($"{result.TestCase.DisplayName},{result.Outcome},{result.Duration},{resourceCount},{randomSeed}");
      }

      writer.Flush();
      _ = logWriter.Status("Results File: " + Path.GetFullPath(writerFilename));
    }
  }
}
