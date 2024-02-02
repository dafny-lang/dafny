using System;
using System.Collections.Generic;
using System.Linq;
using System.Reactive.Subjects;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Extensions.Logging;
using VC;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Various;

/// If any top-level declaration has an attribute `{:neverVerify}`,
/// this verifier will return a task that only completes when cancelled
/// which can be useful to test against race conditions
class SlowVerifier : IProgramVerifier {
  public SlowVerifier(ILogger<DafnyProgramVerifier> logger) {
    verifier = new DafnyProgramVerifier(logger);
  }

  private readonly DafnyProgramVerifier verifier;

  public async Task<IReadOnlyList<IVerificationTask>> GetVerificationTasksAsync(ExecutionEngine engine,
    ResolutionResult resolution, ModuleDefinition moduleDefinition, CancellationToken cancellationToken) {
    var program = resolution.ResolvedProgram;
    var attributes = program.Modules().SelectMany(m => {
      return m.TopLevelDecls.OfType<TopLevelDeclWithMembers>().SelectMany(d => d.Members.Select(member => member.Attributes));
    }).ToList();

    var tasks = await verifier.GetVerificationTasksAsync(engine, resolution, moduleDefinition, cancellationToken);
    if (attributes.Any(a => Attributes.Contains(a, "neverVerify"))) {
      tasks = tasks.Select(t => new NeverVerifiesImplementationTask(t)).ToList();
    }

    return tasks;
  }

  class NeverVerifiesImplementationTask : IVerificationTask {
    private readonly IVerificationTask original;
    private readonly Subject<IVerificationStatus> source;

    public NeverVerifiesImplementationTask(IVerificationTask original) {
      this.original = original;
      source = new();
    }

    public IVerificationStatus CacheStatus => new Stale();
    public ManualSplit Split => original.Split;
    public Boogie.IToken ScopeToken => original.ScopeToken;
    public string ScopeId => original.ScopeId;
    public Boogie.IToken Token => original.Token;

    public IObservable<IVerificationStatus> TryRun() {
      return source;
    }

    public bool IsIdle => false;

    public void Cancel() {
      source.OnError(new TaskCanceledException());
    }
  }
}
