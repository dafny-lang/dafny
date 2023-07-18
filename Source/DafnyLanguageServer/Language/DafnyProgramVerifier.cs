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
      engine = new ExecutionEngine(options, cache);
    }

    private const int TranslatorMaxStackSize = 0x10000000; // 256MB

    public async Task<IReadOnlyList<IImplementationTask>> GetVerificationTasksAsync(CompilationAfterResolution compilation,
      CancellationToken cancellationToken) {
      var program = compilation.Program;
      var errorReporter = (DiagnosticErrorReporter)program.Reporter;

      cancellationToken.ThrowIfCancellationRequested();

      var translated = await DafnyMain.LargeStackFactory.StartNew(() => Translator.Translate(program, errorReporter, new Translator.TranslatorFlags(errorReporter.Options) {
        InsertChecksums = true,
        ReportRanges = true
      }).ToList(), cancellationToken);

      cancellationToken.ThrowIfCancellationRequested();

      if (engine.Options.PrintFile != null) {
        var moduleCount = Translator.VerifiableModules(program).Count();
        foreach (var (suffix, boogieProgram) in translated) {
          var fileName = moduleCount > 1 ? DafnyMain.BoogieProgramSuffix(engine.Options.PrintFile, suffix) : engine.Options.PrintFile;
          ExecutionEngine.PrintBplFile(engine.Options, fileName, boogieProgram, false, false, engine.Options.PrettyPrint);
        }
      }

      return translated.SelectMany(t => {
        var (_, boogieProgram) = t;
        return engine.GetImplementationTasks(boogieProgram);
      }).ToList();
    }

    public void Dispose() {
      engine.Dispose();
    }
  }
}
