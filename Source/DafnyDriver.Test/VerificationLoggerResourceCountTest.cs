using System.Text.Json.Nodes;
using Microsoft.Boogie;
using Microsoft.Dafny;
using VC;
using Token = Microsoft.Dafny.Token;

namespace DafnyDriver.Test;

public class VerificationLoggerResourceCountTest {
  [Theory]
  [InlineData(0, 0, 0L)]
  [InlineData(int.MaxValue - 1, 1, 2147483647L)]
  [InlineData(int.MaxValue, 1, 2147483648L)]
  [InlineData(int.MaxValue, int.MaxValue, 4294967294L)]
  public void TextLoggerPreservesResourceCounts(int firstResourceCount, int secondResourceCount,
    long expectedTotal) {
    using var output = new StringWriter();
    TextVerificationLogger.LogResults(new ProofDependencyManager(), output,
      CreateScopeResult(firstResourceCount, secondResourceCount));

    var log = output.ToString();
    Assert.Contains($"  Overall resource count: {expectedTotal}{Environment.NewLine}", log);
    Assert.Contains(
      $"  Maximum assertion batch resource count: {Math.Max(firstResourceCount, secondResourceCount)}{Environment.NewLine}", log);
    Assert.Contains($"    Resource count: {firstResourceCount}{Environment.NewLine}", log);
    Assert.Contains($"    Resource count: {secondResourceCount}{Environment.NewLine}", log);
  }

  [Theory]
  [InlineData(0, 0, 0L)]
  [InlineData(int.MaxValue - 1, 1, 2147483647L)]
  [InlineData(int.MaxValue, 1, 2147483648L)]
  [InlineData(int.MaxValue, int.MaxValue, 4294967294L)]
  public async Task JsonLoggerPreservesResourceCounts(int firstResourceCount, int secondResourceCount,
    long expectedTotal) {
    using var output = new StringWriter();
    var options = new DafnyOptions(TextReader.Null, output, TextWriter.Null);
    var logger = new JsonVerificationLogger(new ProofDependencyManager(), options.OutputWriter);
    logger.Initialize(new Dictionary<string, string>());

    logger.LogScopeResults(CreateScopeResult(firstResourceCount, secondResourceCount));
    await logger.Flush();

    var log = JsonNode.Parse(output.ToString())!;
    var scope = Assert.Single(log["verificationResults"]!.AsArray())!;
    Assert.Equal(expectedTotal, scope["resourceCount"]!.GetValue<long>());
    Assert.Collection(scope["vcResults"]!.AsArray(),
      result => Assert.Equal(firstResourceCount, result!["resourceCount"]!.GetValue<int>()),
      result => Assert.Equal(secondResourceCount, result!["resourceCount"]!.GetValue<int>()));
  }

  private static VerificationScopeResult CreateScopeResult(params int[] resourceCounts) {
    // Synthetic counts exercise the overflow boundary without an expensive solver run.
    var results = resourceCounts.Select((resourceCount, index) => new VerificationTaskResult(null!,
      new VerificationRunResult(index + 1, 0, DateTime.UnixEpoch, SolverOutcome.Valid, TimeSpan.Zero,
        0, null!, new List<AssertCmd>(), new List<TrackedNodeComponent>(), resourceCount, null,
        new List<Microsoft.Boogie.Declaration>()))).ToList();
    var origin = new Token(1, 1) { Uri = new Uri("file:///test.dfy") };
    return new VerificationScopeResult(new VerificationScope("M", origin), results);
  }
}
