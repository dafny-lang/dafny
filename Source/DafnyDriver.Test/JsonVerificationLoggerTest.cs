using System.Text.Json.Nodes;
using DafnyCore.Verifier;
using Microsoft.Boogie;
using Microsoft.Dafny;
using VC;
using Token = Microsoft.Dafny.Token;

namespace DafnyDriver.Test;

public class JsonVerificationLoggerTest {

  [Fact]
  public async Task VcResultsAreOrderedByVcNum() {
    await WithLogFile(async logFile => {
      var logger = new JsonVerificationLogger(new ProofDependencyManager(), null!);
      logger.Initialize(LogTo(logFile));

      logger.LogScopeResults(new VerificationScopeResult(
        new VerificationScope("M", Origin(1, 1)),
        new List<VerificationTaskResult> { TaskResult(2), TaskResult(1) }));
      await logger.Flush();

      Assert.Equal(new[] { 1, 2 }, VcNums(Read(logFile)));
    });
  }

  [Fact]
  public async Task LegacyVcResultsAreOrderedByVcNum() {
    await WithLogFile(async logFile => {
      var logger = new LegacyJsonVerificationLogger(new ProofDependencyManager(), null!);
      logger.Initialize(LogTo(logFile));

      logger.LogResults(new[] { Entry("M", Origin(1, 1), RunResult(2), RunResult(1)) });
      await logger.DisposeAsync();

      Assert.Equal(new[] { 1, 2 }, VcNums(Read(logFile)));
    });
  }

  /// Goes through RaiseTestLoggerEvents so that the ordering of the printer's ConcurrentBag is
  /// covered too. "A" is recorded after "B", and its two scopes share one token and are recorded
  /// so that the bag yields them the wrong way round, which only the name tiebreak corrects.
  [Fact]
  public Task LegacyScopesAreOrderedBySourcePositionThenName() {
    return WithLogFile(logFile => {
      var options = new DafnyOptions(TextReader.Null, TextWriter.Null, TextWriter.Null);
      var printer = new DafnyConsolePrinter(options);
      options.Printer = printer;
      options.Set(CommonOptionBag.VerificationLogFormat, new List<string> { $"json;LogFileName={logFile}" });

      printer.VerificationResults.Add(Entry("B (correctness)", Origin(20, 1), RunResult(1)));
      printer.VerificationResults.Add(Entry("A (correctness)", Origin(10, 1), RunResult(1)));
      printer.VerificationResults.Add(Entry("A (well-formedness)", Origin(10, 1), RunResult(1)));

      LegacyVerificationResultLogger.RaiseTestLoggerEvents(options, new ProofDependencyManager());

      Assert.Equal(new[] { "A (correctness)", "A (well-formedness)", "B (correctness)" },
        ScopeNames(Read(logFile)));
      return Task.CompletedTask;
    });
  }

  private static async Task WithLogFile(Func<string, Task> test) {
    var logFile = Path.GetTempFileName();
    try {
      await test(logFile);
    }
    finally {
      File.Delete(logFile);
    }
  }

  private static Dictionary<string, string> LogTo(string logFile) {
    return new Dictionary<string, string> { ["LogFileName"] = logFile };
  }

  private static Token Origin(int line, int col) {
    return new Token(line, col) { Uri = new Uri("file:///test.dfy") };
  }

  private static DafnyConsolePrinter.ConsoleLogEntry Entry(string name, Token origin,
    params VerificationRunResultPartialCopy[] runResults) {
    return new DafnyConsolePrinter.ConsoleLogEntry(
      new DafnyConsolePrinter.ImplementationLogEntry(name, origin),
      new DafnyConsolePrinter.VerificationResultLogEntry(
        VcOutcome.Correct, TimeSpan.Zero, 0, runResults.ToList(), new List<Counterexample>()));
  }

  private static VerificationRunResultPartialCopy RunResult(int vcNum) {
    return new VerificationRunResultPartialCopy(vcNum, DateTime.UnixEpoch, TimeSpan.Zero,
      SolverOutcome.Valid, new List<AssertCmdPartialCopy>(), new List<TrackedNodeComponent>(),
      new List<Axiom>(), 0);
  }

  private static VerificationTaskResult TaskResult(int vcNum) {
    return LegacyJsonVerificationLogger.VCResultLogEntryToPartialVerificationRunResult(RunResult(vcNum));
  }

  private static JsonNode Read(string logFile) {
    return JsonNode.Parse(File.ReadAllText(logFile))!;
  }

  private static IEnumerable<string> ScopeNames(JsonNode log) {
    return log["verificationResults"]!.AsArray().Select(result => (string)result!["name"]!);
  }

  private static IEnumerable<int> VcNums(JsonNode log) {
    return log["verificationResults"]!.AsArray()
      .SelectMany(result => result!["vcResults"]!.AsArray())
      .Select(vcResult => (int)vcResult!["vcNum"]!);
  }
}
