using Microsoft.Boogie;
using Microsoft.Extensions.Logging;
using Microsoft.Extensions.Options;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.Workspace;

namespace Microsoft.Dafny.LanguageServer.Language {
  /// <summary>
  /// dafny-lang based implementation of the program verifier. Since it makes use of static members,
  /// any access is synchronized. Moreover, it ensures that exactly one instance exists over the whole
  /// application lifetime.
  /// </summary>
  /// <remarks>
  /// dafny-lang makes use of static members and assembly loading. Since thread-safety of this is not guaranteed,
  /// this verifier serializes all invocations.
  /// </remarks>
  public class DafnyProgramVerifier : IProgramVerifier {
    private readonly VerificationResultCache cache = new();
    private readonly ExecutionEngine engine;

    public DafnyProgramVerifier(
      ILogger<DafnyProgramVerifier> logger,
      IOptions<VerifierOptions> options
      ) {
      var engineOptions = DafnyOptions.O;
      engineOptions.VcsCores = GetConfiguredCoreCount(options.Value);
      engineOptions.TimeLimit = options.Value.TimeLimit;
      engineOptions.VerifySnapshots = (int)options.Value.VerifySnapshots;
      // TODO This may be subject to change. See Microsoft.Boogie.Counterexample
      //      A dash means write to the textwriter instead of a file.
      // https://github.com/boogie-org/boogie/blob/b03dd2e4d5170757006eef94cbb07739ba50dddb/Source/VCGeneration/Couterexample.cs#L217
      engineOptions.ModelViewFile = "-";
      BatchObserver = new AssertionBatchCompletedObserver(logger, options.Value.GutterStatus);

      engineOptions.Printer = BatchObserver;
      engine = new ExecutionEngine(engineOptions, cache);
    }

    private static int GetConfiguredCoreCount(VerifierOptions options) {
      return options.VcsCores == 0
        ? Math.Max(1, Environment.ProcessorCount / 2)
        : Convert.ToInt32(options.VcsCores);
    }

    private const int TranslatorMaxStackSize = 0x10000000; // 256MB
    static readonly ThreadTaskScheduler TranslatorScheduler = new(TranslatorMaxStackSize);
    public AssertionBatchCompletedObserver BatchObserver { get; }

    public async Task<IReadOnlyList<IImplementationTask>> GetVerificationTasksAsync(DafnyDocument document, CancellationToken cancellationToken) {
      var program = document.Program;
      var errorReporter = (DiagnosticErrorReporter)program.Reporter;

      cancellationToken.ThrowIfCancellationRequested();

      var translated = await Task.Factory.StartNew(() => Translator.Translate(program, errorReporter, new Translator.TranslatorFlags {
        InsertChecksums = true,
        ReportRanges = true
      }).ToList(), cancellationToken, TaskCreationOptions.None, TranslatorScheduler);

      cancellationToken.ThrowIfCancellationRequested();

      var tasks = translated.SelectMany(t => {
        var (_, boogieProgram) = t;
        var results = engine.GetImplementationTasks(boogieProgram);
        return results;
      });
      return tasks.
        OrderBy(t => t.Implementation.Priority).
        CreateOrderedEnumerable(
          t => document.LastTouchedVerifiables.IndexOf(t.Implementation.tok.GetLspPosition()),
          null, true).
        ToList();
    }

    public IObservable<AssertionBatchResult> BatchCompletions => BatchObserver.CompletedBatches;
  }
}
