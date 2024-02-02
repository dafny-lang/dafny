using Microsoft.Boogie;
using Microsoft.Extensions.Logging;
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
    private readonly ILogger<DafnyProgramVerifier> logger;
    private readonly SemaphoreSlim mutex = new(1);

    public DafnyProgramVerifier(ILogger<DafnyProgramVerifier> logger) {
      this.logger = logger;
    }

    public async Task<IReadOnlyList<IVerificationTask>> GetVerificationTasksAsync(ExecutionEngine engine,
      ResolutionResult resolution,
      ModuleDefinition moduleDefinition,
      CancellationToken cancellationToken) {

      if (!BoogieGenerator.ShouldVerifyModule(resolution.ResolvedProgram, moduleDefinition)) {
        throw new Exception("tried to get verification tasks for a module that is not verified");
      }

      await mutex.WaitAsync(cancellationToken);
      try {

        var program = resolution.ResolvedProgram;
        var errorReporter = (ObservableErrorReporter)program.Reporter;

        cancellationToken.ThrowIfCancellationRequested();

        var boogieProgram = await DafnyMain.LargeStackFactory.StartNew(() => {
          Type.ResetScopes();
          var translatorFlags = new BoogieGenerator.TranslatorFlags(errorReporter.Options) {
            InsertChecksums = 0 < engine.Options.VerifySnapshots,
            ReportRanges = program.Options.Get(DafnyConsolePrinter.ShowSnippets)
          };
          var translator = new BoogieGenerator(errorReporter, resolution.ResolvedProgram.ProofDependencyManager, translatorFlags);
          return translator.DoTranslation(resolution.ResolvedProgram, moduleDefinition);
        }, cancellationToken);
        var suffix = moduleDefinition.SanitizedName;

        cancellationToken.ThrowIfCancellationRequested();

        if (engine.Options.PrintFile != null) {
          var moduleCount = BoogieGenerator.VerifiableModules(program).Count();
          var fileName = moduleCount > 1 ? DafnyMain.BoogieProgramSuffix(engine.Options.PrintFile, suffix) : engine.Options.PrintFile;
          ExecutionEngine.PrintBplFile(engine.Options, fileName, boogieProgram, false, false, engine.Options.PrettyPrint);
        }

        var tasksFromBoogie = engine.GetVerificationTasks(boogieProgram);

        // Ordering is required to let gutter icon tests behave more deterministically
        // In situations where there are multiple valid orders of execution
        // In particular, GitIssue3821GutterIgnoredProblem fails without this
        // We can consider turning off that test so we do not need this hack
        // Better would be to compute gutter icons on the client
        var ordered = tasksFromBoogie.
          OrderBy(s => s.ScopeToken).
          ThenByDescending(s => s.ScopeId).
          ThenBy(s => s.Token).ToList();
        return ordered;
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
