using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.CommandLine;
using System.Linq;
using System.Reactive.Subjects;
using System.Text.Json;
using System.Text.Json.Nodes;
using System.Threading;
using System.Threading.Tasks;
using DafnyDriver.Commands;
using Microsoft.Boogie;

namespace Microsoft.Dafny;

static class MeasureComplexityCommand {
  public static IEnumerable<Option> Options => new Option[] {
    Iterations,
    RandomSeed,
    Format,
    TopX,
    VerifyCommand.FilterSymbol,
    VerifyCommand.FilterPosition,
  }.Concat(DafnyCommands.VerificationOptions).
    Concat(DafnyCommands.ResolverOptions).
    Concat(DafnyCommands.ConsoleOutputOptions);

  static MeasureComplexityCommand() {
    DafnyOptions.RegisterLegacyBinding(Iterations, (o, v) => o.RandomizeVcIterations = (int)v);
    DafnyOptions.RegisterLegacyBinding(RandomSeed, (o, v) => o.RandomSeed = (int)v);

    OptionRegistry.RegisterOption(Iterations, OptionScope.Cli);
    OptionRegistry.RegisterOption(RandomSeed, OptionScope.Cli);
    OptionRegistry.RegisterOption(Format, OptionScope.Cli);
    OptionRegistry.RegisterOption(TopX, OptionScope.Cli);
  }

  enum ComplexityFormat { Text, Json, LineBased }
  private static readonly Option<ComplexityFormat> Format = new("--format", 
    $"Specify the format in which the complexity data is presented");
  
  private static readonly Option<uint> TopX = new("--worst-amount", () => 10U,
    $"Configures the amount of worst performing verification tasks that are reported.");

  private static readonly Option<uint> RandomSeed = new("--random-seed", () => 0U,
    $"Turn on randomization of the input that Dafny passes to the SMT solver and turn on randomization in the SMT solver itself. Certain Dafny proofs are complex in the sense that changes to the proof that preserve its meaning may cause its verification result to change. This option simulates meaning-preserving changes to the proofs without requiring the user to actually make those changes. The proof changes are renaming variables and reordering declarations in the SMT input passed to the solver, and setting solver options that have similar effects.");

  private static readonly Option<uint> Iterations = new("--iterations", () => 1U,
    $"Attempt to verify each proof n times with n random seeds, each seed derived from the previous one. {RandomSeed.Name} can be used to specify the first seed, which will otherwise be 0.") {
    ArgumentHelpName = "n"
  };

  public static Command Create() {
    var result = new Command("measure-complexity", "(Experimental) Measure the complexity of verifying the program.");
    result.AddArgument(DafnyCommands.FilesArgument);
    foreach (var option in Options) {
      result.AddOption(option);
    }
    DafnyNewCli.SetHandlerUsingDafnyOptionsContinuation(result, (options, _) => Execute(options));
    return result;
  }

  private static async Task<int> Execute(DafnyOptions options) {
    if (options.Get(CommonOptionBag.VerificationCoverageReport) != null) {
      options.TrackVerificationCoverage = true;
    }

    var compilation = CliCompilation.Create(options);
    compilation.Start();

    var resolution = await compilation.Resolution;
    if (resolution != null) {
      Subject<CanVerifyResult> verificationResults = new();

      // We should redesign the output of this command 
      // It should start out with a summary that reports how many proofs are brittle, and shows statistical data,
      // such as averages and standard-deviations.
      // For error diagnostics, we should group duplicates and say how often they occur.
      // Performance data of individual verification tasks (VCs) should be grouped by VcNum (the assertion batch).
      VerifyCommand.ReportVerificationDiagnostics(compilation, verificationResults);
      var summaryReported = ReportResourceSummary(compilation, verificationResults);
      var proofDependenciesReported = VerifyCommand.ReportProofDependencies(compilation, resolution, verificationResults);
      var verificationResultsLogged = VerifyCommand.LogVerificationResults(compilation, resolution, verificationResults);

      await RunVerificationIterations(options, compilation, verificationResults);
      await summaryReported;
      await verificationResultsLogged;
      await proofDependenciesReported;
    }

    return await compilation.GetAndReportExitCode();
  }

  record TaskIterationStatistics {
    public ConcurrentBag<int> ResourceCounts = new();
    public ConcurrentBag<double> VerificationTimes = new();
    public int Timeouts;
    public int ResourceOuts;
    public int Failures;
    public int Measurements;
  }
  
  public static async Task ReportResourceSummary(
    CliCompilation cliCompilation,
    IObservable<CanVerifyResult> verificationResults) {

    var allStatistics = new ConcurrentDictionary<string, TaskIterationStatistics>();
    PriorityQueue<VerificationTaskResult, int> worstPerformers = new();

    var totalResources = 0L;
    var worstAmount = cliCompilation.Options.Get(TopX);
    verificationResults.Subscribe(result => {
      foreach (var taskResult in result.Results) {
        var runResult = taskResult.Result;
        totalResources += runResult.ResourceCount;
        worstPerformers.Enqueue(taskResult, runResult.ResourceCount);
        if (worstPerformers.Count > worstAmount) {
          worstPerformers.Dequeue();
        }

        var key = taskResult.Task.Split.Implementation.Name + taskResult.Task.Split.Token.ShortName;
        var statistics = allStatistics.GetOrAdd(key, _ => new TaskIterationStatistics());
        var failed = false;
        if (runResult.Outcome == SolverOutcome.Valid) {
          statistics.ResourceCounts.Add(runResult.ResourceCount);
          statistics.VerificationTimes.Add(runResult.RunTime.TotalSeconds);
        } else if (runResult.Outcome == SolverOutcome.TimeOut) {
          Interlocked.Increment(ref statistics.Timeouts);
          failed = true;
        } else if (runResult.Outcome == SolverOutcome.OutOfResource) {
          Interlocked.Increment(ref statistics.ResourceOuts);
          failed = true;
        } else if (runResult.Outcome == SolverOutcome.Invalid) {
          failed = true;
        }

        if (failed) {
          Interlocked.Increment(ref statistics.Failures);
        }
        Interlocked.Increment(ref statistics.Measurements);
      }
    });
    await verificationResults.WaitForComplete();
    var output = cliCompilation.Options.OutputWriter;
    var decreasingWorst = new Stack<VerificationTaskResult>();
    while (worstPerformers.Count > 0) {
      decreasingWorst.Push(worstPerformers.Dequeue());
    }
    if (cliCompilation.Options.Get(Format) == ComplexityFormat.LineBased) {
      var lines = decreasingWorst.GroupBy(t => t.Task.Token.line).
        OrderBy(g => g.Key).
        Select(g => g.Key + ", " + Math.Floor(g.Average(i => i.Result.ResourceCount)));
      
      await output.WriteLineAsync($"Average resource for each line:\n" + string.Join("\n", lines));
    } 
    else if (cliCompilation.Options.Get(Format) == ComplexityFormat.Text)
    {
      await output.WriteLineAsync($"The total consumed resources are {totalResources}");
      await output.WriteLineAsync($"The most demanding {worstAmount} verification tasks consumed these resources:");
      foreach (var performer in decreasingWorst) {
        var location = BoogieGenerator.ToDafnyToken(false, performer.Task.Token).TokenToString(cliCompilation.Options);
        await output.WriteLineAsync($"{location}: {performer.Result.ResourceCount}");
      }
    } else if (cliCompilation.Options.Get(Format) == ComplexityFormat.Json) {
      var json = new JsonObject {
        ["totalResources"] = totalResources,
        ["worstPerforming"] = new JsonArray(decreasingWorst.Select(task => new JsonObject {
          ["location"] = SerializeToken(task.Task.Token),
          ["resourceCount"] = task.Result.ResourceCount
        }).ToArray<JsonNode>()),
        ["taskData"] = new JsonArray(allStatistics.Select(entry => {
          var (stdDevRc, averageRc) = entry.Value.ResourceCounts.ToList().CalculateStdDev();
          var (stdDevVt, averageVt) = entry.Value.VerificationTimes.ToList().CalculateStdDev();
          var failuresAndHighVariations = entry.Value.Failures + entry.Value.ResourceCounts.Count(rc => rc > averageRc * 2);
          return new JsonObject {
            ["key"] = entry.Key,
            ["rcs"] = new JsonArray(entry.Value.ResourceCounts.Select(r => JsonValue.Create(r)).ToArray<JsonNode>()),
            ["vts"] = new JsonArray(entry.Value.VerificationTimes.Select(r => JsonValue.Create(r)).ToArray<JsonNode>()),
            ["averageRc"] = averageRc,
            ["standardDeviationRc"] = stdDevRc,
            ["relativeStandardDeviationRc"] = stdDevRc / averageRc,
            ["averageVt"] = averageVt,
            ["standardDeviationVt"] = stdDevVt,
            ["relativeStandardDeviationVt"] = stdDevVt / averageVt,
            ["timeouts"] = entry.Value.Timeouts,
            ["resourceOuts"] = entry.Value.ResourceOuts,
            ["failures"] = entry.Value.Failures,
            ["relFailures"] = (double)entry.Value.Failures / entry.Value.Measurements,
            ["failuresAndHighVariations"] = failuresAndHighVariations,
            ["relFailuresAndHighVariations"] = (double)failuresAndHighVariations / entry.Value.Measurements,
          };
        }).ToArray<JsonNode>())
      };
      var outputString = json.ToJsonString(new JsonSerializerOptions { WriteIndented = false });
      await output.WriteLineAsync(outputString);
    }
  }

  private static JsonObject SerializeToken(Boogie.IToken tok) {
    return new JsonObject {
      ["uri"] = BoogieGenerator.ToDafnyToken(false, tok).Uri.AbsoluteUri,
      ["range"] = DiagnosticMessageData.SerializeRange(tok)
    };
  }
  
  private static async Task RunVerificationIterations(DafnyOptions options, CliCompilation compilation,
    IObserver<CanVerifyResult> verificationResultsObserver) {
    int iterationSeed = (int)options.Get(RandomSeed);
    var random = new Random(iterationSeed);
    var iterations = (int)options.Get(Iterations);
    foreach (var iteration in Enumerable.Range(0, iterations)) {
      if (options.Get(CommonOptionBag.ProgressOption) >= CommonOptionBag.ProgressLevel.Iteration) {
        await options.OutputWriter.WriteLineAsync(
          $"{DateTime.Now.ToLocalTime()}: Starting verification of iteration {iteration + 1}/{iterations} with seed {iterationSeed}");
      }
      try {
        await foreach (var result in compilation.VerifyAllLazily(iterationSeed)) {
          verificationResultsObserver.OnNext(result);
        }
      } catch (Exception e) {
        verificationResultsObserver.OnError(e);
      }
      iterationSeed = random.Next();
    }
    verificationResultsObserver.OnCompleted();
  }
}
public static class ExtensionsClass
{
  public static (double StdDev, double Average) CalculateStdDev(this IReadOnlyList<double> values)
  {
    if (values.Count == 0) {
      return (-1, -1);
    }
    
    if (values.Count > 1)
    {
      // Compute the Average
      double avg = values.Average();

      // Perform the Sum of (value-avg)^2
      double sum = values.Sum(d => (d - avg) * (d - avg));

      return (Math.Sqrt(sum / values.Count), avg);
    }

    return (0, values[0]);
  }
  
  public static (double StdDev, double Average) CalculateStdDev(this IReadOnlyList<int> values)
  {
    if (values.Count == 0) {
      return (-1, -1);
    }
    
    if (values.Count > 1)
    {
      // Compute the Average
      double avg = values.Average();

      // Perform the Sum of (value-avg)^2
      double sum = values.Sum(d => (d - avg) * (d - avg));

      return (Math.Sqrt(sum / values.Count), avg);
    }

    return (0, values[0]);
  }
}
