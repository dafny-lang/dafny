using System;
using System.Linq;
using System.Reactive.Linq;
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

  public ProgramVerificationObjects GetImplementationTasks(DafnyDocument document)
  {
    var program = document.Program;
    var attributes = program.Modules().SelectMany(m => {
      return m.TopLevelDecls.OfType<TopLevelDeclWithMembers>().SelectMany(d => d.Members.Select(member => member.Attributes));
    }).ToList();

    var (tasks, observer) = verifier.GetImplementationTasks(document);
    if (attributes.Any(a => Attributes.Contains(a, "neverVerify"))) {
      tasks = tasks.Select(t => new NeverVerifiesImplementationTask(t)).ToList();
    }

    return new ProgramVerificationObjects(tasks, observer);
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