using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reactive.Subjects;
using System.Text.Json.Nodes;
using System.Threading.Tasks;
using DafnyDriver.Commands;
using Microsoft.Boogie;
using Microsoft.Dafny;
using VC;
using Xunit;

namespace DafnyDriver.Test;

/// <summary>
/// Each verification run reports its resource count as an int, but a scope sums them, and a
/// program sums the scopes. Three expensive assertion batches are enough to pass int.MaxValue,
/// at which point the sum silently wrapped negative (https://github.com/dafny-lang/dafny/issues/6281).
/// </summary>
public class ResourceCountOverflowTest {

  private const int PerRunResourceCount = 800_000_000;
  private const long ExpectedTotal = 3L * PerRunResourceCount; // 2_400_000_000 > int.MaxValue

  private static VerificationScopeResult ScopeWithThreeExpensiveRuns() {
    var results = Enumerable.Range(0, 3).Select(vcNum =>
      new VerificationTaskResult(null,
        new VerificationRunResult(vcNum, 0, System.DateTime.UnixEpoch, SolverOutcome.Valid,
          System.TimeSpan.Zero, 0, null!, new List<AssertCmd>(), new List<TrackedNodeComponent>(),
          PerRunResourceCount, null, new List<Microsoft.Boogie.Declaration>()))).ToList();
    return new VerificationScopeResult(new VerificationScope("MyMethod", Microsoft.Boogie.Token.NoToken), results);
  }

  [Fact]
  public void TextLoggerReportsTotalWiderThanInt() {
    var writer = new StringWriter();
    TextVerificationLogger.LogResults(new ProofDependencyManager(), writer, ScopeWithThreeExpensiveRuns());
    Assert.Contains($"Overall resource count: {ExpectedTotal}", writer.ToString());
  }

  /// <summary>
  /// --performance-stats accumulates into a separate field, which wrapped silently rather than
  /// throwing, so this is the only mode where the defect produced a plausible-looking negative
  /// number instead of a crash.
  /// </summary>
  [Fact]
  public async Task PerformanceStatisticsReportTotalWiderThanInt() {
    var writer = new StringWriter();
    var options = DafnyOptions.CreateUsingOldParser(writer);
    options.Set(VerifyCommand.PerformanceStatisticsOption, 1);
    var compilation = CliCompilation.Create(options);

    var results = new Subject<CanVerifyResult>();
    var summary = VerifyCommand.ReportVerificationSummary(compilation, results);
    results.OnNext(new CanVerifyResult(null!, ScopeWithThreeExpensiveRuns().Results));
    results.OnCompleted();
    await summary;

    Assert.Contains($"Total resources used is {ExpectedTotal}", writer.ToString());
  }

  /// <summary>
  /// measure-complexity keeps its own accumulator. Its --worst-amount option is private, but it
  /// defaults to 10, which is more than the three runs here, so the summary is reachable anyway.
  /// </summary>
  [Fact]
  public async Task MeasureComplexityReportsTotalWiderThanInt() {
    var writer = new StringWriter();
    var options = DafnyOptions.CreateUsingOldParser(writer);
    var compilation = CliCompilation.Create(options);

    var results = new Subject<CanVerifyResult>();
    var summary = MeasureComplexityCommand.ReportResourceSummary(compilation, results);
    results.OnNext(new CanVerifyResult(null!, ScopeWithThreeExpensiveRuns().Results));
    results.OnCompleted();
    await summary;

    Assert.Contains($"The total consumed resources are {ExpectedTotal}", writer.ToString());
  }

  /// <summary>
  /// The JSON logger sums independently of the text logger, and its value is consumed by tools
  /// rather than read by a person, so a wrapped negative number here is the least likely to be
  /// noticed. Lit tests cannot cover it: logger .expect files scrub resource counts with wildcards.
  /// </summary>
  [Fact]
  public async Task JsonLoggerRoundTripsTotalWiderThanInt() {
    var logFile = Path.Combine(Path.GetTempPath(), Path.GetRandomFileName() + ".json");
    var options = DafnyOptions.CreateUsingOldParser(new StringWriter());
    var logger = new JsonVerificationLogger(new ProofDependencyManager(),
      new HumanReadableOutputWriter(options));
    logger.Initialize(new Dictionary<string, string> { ["LogFileName"] = logFile });
    logger.LogScopeResults(ScopeWithThreeExpensiveRuns());
    await logger.Flush();

    var scopes = JsonNode.Parse(await File.ReadAllTextAsync(logFile))!["verificationResults"]!.AsArray();
    File.Delete(logFile);
    Assert.Equal(ExpectedTotal, scopes[0]!["resourceCount"]!.GetValue<long>());
  }
}
