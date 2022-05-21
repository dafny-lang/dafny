using System;
using System.Collections.Generic;
using System.Linq;
using System.Reactive.Linq;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Logging;
using Microsoft.Extensions.Options;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Various;

/// If any top-level declaration has an attribute `{:neverVerify}`,
/// this verifier will return a task that only completes when cancelled
/// which can be useful to test against race conditions
class SlowVerifier : IProgramVerifier {
  public SlowVerifier(ILogger<DafnyProgramVerifier> logger, IOptions<VerifierOptions> options) {
    verifier = DafnyProgramVerifier.Create(logger, options);
  }

  private readonly DafnyProgramVerifier verifier;

  public IReadOnlyList<IImplementationTask> Verify(DafnyDocument document,
    IVerificationProgressReporter progressReporter) {
    var program = document.Program;
    var attributes = program.Modules().SelectMany(m => {
      return m.TopLevelDecls.OfType<TopLevelDeclWithMembers>().SelectMany(d => d.Members.Select(member => member.Attributes));
    }).ToList();

    var originalResult = verifier.Verify(document, progressReporter);
    if (attributes.Any(a => Attributes.Contains(a, "neverVerify"))) {
      return new List<IImplementationTask>
        { new NeverVerifiesImplementationTask(originalResult[0]) };
    }

    return originalResult;
  }

  class NeverVerifiesImplementationTask : IImplementationTask {
    private readonly IImplementationTask original;
    private readonly TaskCompletionSource<VerificationResult> source;

    public NeverVerifiesImplementationTask(IImplementationTask original) {
      this.original = original;
      source = new TaskCompletionSource<VerificationResult>();
    }

    public IObservable<VerificationStatus> ObservableStatus => Observable.Empty<VerificationStatus>();
    public VerificationStatus CurrentStatus => VerificationStatus.Running;
    public ProcessedProgram ProcessedProgram => original.ProcessedProgram;
    public Implementation Implementation => original.Implementation;
    public Task<VerificationResult> ActualTask => source.Task;

    public void Run() {

    }

    public void Cancel() {
      source.SetCanceled();
    }
  }
}