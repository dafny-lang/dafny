using Microsoft.Boogie;
using Microsoft.Extensions.Logging;
using Microsoft.Extensions.Options;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.Workspace;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

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
  public class DafnyProgramVerifier : IProgramVerifier, IDisposable {
    private readonly VerificationResultCache cache = new();
    private readonly ExecutionEngine engine;

    public DafnyProgramVerifier(
      ILogger<DafnyProgramVerifier> logger,
      DafnyOptions options
      ) {
      // TODO This may be subject to change. See Microsoft.Boogie.Counterexample
      //      A dash means write to the textwriter instead of a file.
      // https://github.com/boogie-org/boogie/blob/b03dd2e4d5170757006eef94cbb07739ba50dddb/Source/VCGeneration/Couterexample.cs#L217
      options.ModelViewFile = "-";

      options.Printer = new OutputLogger(logger);
      engine = new ExecutionEngine(options, cache);
    }

    private const int TranslatorMaxStackSize = 0x10000000; // 256MB
    static readonly ThreadTaskScheduler TranslatorScheduler = new(TranslatorMaxStackSize);

    public async Task<IReadOnlyList<IImplementationTask>> GetVerificationTasksAsync(DocumentAfterResolution document,
      CancellationToken cancellationToken) {
      var program = document.Program;
      var errorReporter = (DiagnosticErrorReporter)program.Reporter;

      cancellationToken.ThrowIfCancellationRequested();

      var translated = await Task.Factory.StartNew(() => Translator.Translate(program, errorReporter, new Translator.TranslatorFlags(errorReporter.Options) {
        InsertChecksums = true,
        ReportRanges = true
      }).ToList(), cancellationToken, TaskCreationOptions.None, TranslatorScheduler);

      cancellationToken.ThrowIfCancellationRequested();

      return translated.SelectMany(t => {
        var (_, boogieProgram) = t;
        var results = engine.GetImplementationTasks(boogieProgram);
        return results;
      }).ToList();
    }

    public void Dispose() {
      engine.Dispose();
    }
  }
}
