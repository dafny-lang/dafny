using System.Text.RegularExpressions;
using DafnyCore.Verifier;
using Microsoft.Boogie;
using Microsoft.Dafny;
using VC;
using Token = Microsoft.Boogie.Token;

namespace DafnyDriver.Test;

public class JsonVerificationLoggerTest {
  // The fallback writer stays unused: Initialize is given a LogFileName, so each logger
  // writes there instead.

  [Fact]
  public async Task VcResultsAreOrderedByVcNum() {
    var logFile = Path.GetTempFileName();
    var logger = new JsonVerificationLogger(new ProofDependencyManager(), null!);
    logger.Initialize(new Dictionary<string, string> { ["LogFileName"] = logFile });

    logger.LogScopeResults(new VerificationScopeResult(
      new VerificationScope("M", Token.NoToken),
      new List<VerificationTaskResult> { TaskResult(2), TaskResult(1) }));
    await logger.Flush();

    Assert.Equal(new[] { 1, 2 }, LoggedVcNums(logFile));
  }

  [Fact]
  public async Task LegacyVcResultsAreOrderedByVcNum() {
    var logFile = Path.GetTempFileName();
    var logger = new LegacyJsonVerificationLogger(new ProofDependencyManager(), null!);
    logger.Initialize(new Dictionary<string, string> { ["LogFileName"] = logFile });

    logger.LogResults(new[] {
      new DafnyConsolePrinter.ConsoleLogEntry(
        new DafnyConsolePrinter.ImplementationLogEntry("M", Token.NoToken),
        new DafnyConsolePrinter.VerificationResultLogEntry(
          VcOutcome.Correct, TimeSpan.Zero, 0,
          new List<VerificationRunResultPartialCopy> { RunResult(2), RunResult(1) },
          new List<Counterexample>()))
    });
    await logger.DisposeAsync();

    Assert.Equal(new[] { 1, 2 }, LoggedVcNums(logFile));
  }

  private static VerificationRunResultPartialCopy RunResult(int vcNum) {
    return new VerificationRunResultPartialCopy(vcNum, DateTime.UnixEpoch, TimeSpan.Zero,
      SolverOutcome.Valid, new List<AssertCmdPartialCopy>(), new List<TrackedNodeComponent>(),
      new List<Axiom>(), 0);
  }

  private static VerificationTaskResult TaskResult(int vcNum) {
    return LegacyJsonVerificationLogger.VCResultLogEntryToPartialVerificationRunResult(RunResult(vcNum));
  }

  private static IEnumerable<int> LoggedVcNums(string logFile) {
    return Regex.Matches(File.ReadAllText(logFile), "\"vcNum\":(\\d+)")
      .Select(match => int.Parse(match.Groups[1].Value));
  }
}
