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
    private readonly ILogger<DafnyProgramVerifier> logger;
    private readonly SemaphoreSlim mutex = new(1);

    public DafnyProgramVerifier(ILogger<DafnyProgramVerifier> logger) {
      this.logger = logger;
    }

    public async Task<IReadOnlyList<IImplementationTask>> GetVerificationTasksAsync(ExecutionEngine boogieEngine,
      CompilationAfterResolution compilation,
      ModuleDefinition moduleDefinition,
      CancellationToken cancellationToken) {
      var engine = boogieEngine;

      var verifiableModules = BoogieGenerator.VerifiableModules(compilation.Program);
      if (!verifiableModules.Contains(moduleDefinition)) {
        throw new Exception("tried to get verification tasks for a module that is not verified");
      }

      await mutex.WaitAsync(cancellationToken);
      try {

        var program = compilation.Program;
        var errorReporter = (DiagnosticErrorReporter)program.Reporter;

        cancellationToken.ThrowIfCancellationRequested();

        var boogieProgram = await DafnyMain.LargeStackFactory.StartNew(() => {
          Type.ResetScopes();
          var translatorFlags = new BoogieGenerator.TranslatorFlags(errorReporter.Options) {
            InsertChecksums = 0 < engine.Options.VerifySnapshots,
            ReportRanges = true
          };
          var translator = new BoogieGenerator(errorReporter, compilation.Program.ProofDependencyManager, translatorFlags);
          return translator.DoTranslation(compilation.Program, moduleDefinition);
        }, cancellationToken);
        var suffix = moduleDefinition.SanitizedName;

        cancellationToken.ThrowIfCancellationRequested();

        if (engine.Options.PrintFile != null) {
          var moduleCount = BoogieGenerator.VerifiableModules(program).Count();
          var fileName = moduleCount > 1 ? DafnyMain.BoogieProgramSuffix(engine.Options.PrintFile, suffix) : engine.Options.PrintFile;
          ExecutionEngine.PrintBplFile(engine.Options, fileName, boogieProgram, false, false, engine.Options.PrettyPrint);
        }

        return engine.GetImplementationTasks(boogieProgram);
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
