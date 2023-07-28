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
  public class DafnyProgramVerifier : IProgramVerifier {
    private readonly SemaphoreSlim mutex = new(1);

    public DafnyProgramVerifier(ILogger<DafnyProgramVerifier> logger) {
    }

    public async Task<IReadOnlyList<IImplementationTask>> GetVerificationTasksAsync(
      ExecutionEngine engine,
      CompilationAfterResolution compilation,
      CancellationToken cancellationToken) {
      await mutex.WaitAsync(cancellationToken);
      try {

        var program = compilation.Program;
        var errorReporter = (DiagnosticErrorReporter)program.Reporter;

        cancellationToken.ThrowIfCancellationRequested();

        var flags = new Translator.TranslatorFlags(errorReporter.Options) {
          InsertChecksums = true,
          ReportRanges = true
        };

        var verifiableModules = Translator.VerifiableModules(program).ToList();
        var tasks = verifiableModules.Select(async outerModule => {
          var boogieProgram = await DafnyMain.LargeStackFactory.StartNew(
            () => {
              Type.ResetScopes();

              var translator = new Translator(program.Reporter, flags);
              var boogieProgram = translator.DoTranslation(program, outerModule);

              if (engine.Options.PrintFile != null) {
                var suffix = outerModule.SanitizedName;

                var fileName = verifiableModules.Count > 1
                  ? DafnyMain.BoogieProgramSuffix(engine.Options.PrintFile, suffix)
                  : engine.Options.PrintFile;
                ExecutionEngine.PrintBplFile(engine.Options, fileName, boogieProgram, false, false,
                  engine.Options.PrettyPrint);
              }

              return boogieProgram;
            }, cancellationToken);

          cancellationToken.ThrowIfCancellationRequested();
          return engine.GetImplementationTasks(boogieProgram);
        });

        var tasksPerModule = await Task.WhenAll(tasks);
        return tasksPerModule.SelectMany(x => x).ToList();
      }
      finally {
        mutex.Release();
      }
    }

    public void Dispose() {
      mutex.Dispose();
    }
  }
}
