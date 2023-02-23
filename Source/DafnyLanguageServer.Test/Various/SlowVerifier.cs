using System;
using System.Collections.Generic;
using System.Linq;
using System.Reactive.Subjects;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Logging;
using Microsoft.Extensions.Options;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Various;

/// If any top-level declaration has an attribute `{:neverVerify}`,
/// this verifier will return a task that only completes when cancelled
/// which can be useful to test against race conditions
class SlowVerifier : IProgramVerifier {
  public SlowVerifier(ILogger<DafnyProgramVerifier> logger, DafnyOptions options) {
    verifier = new DafnyProgramVerifier(logger, options);
  }

  private readonly DafnyProgramVerifier verifier;

  public async Task<IReadOnlyList<IImplementationTask>> GetVerificationTasksAsync(DocumentAfterResolution document, CancellationToken cancellationToken) {
    var program = document.Program;
    var attributes = program.Modules().SelectMany(m => {
      return m.TopLevelDecls.OfType<TopLevelDeclWithMembers>().SelectMany(d => d.Members.Select(member => member.Attributes));
    }).ToList();

    var tasks = await verifier.GetVerificationTasksAsync(document, cancellationToken);
    if (attributes.Any(a => Attributes.Contains(a, "neverVerify"))) {
      tasks = tasks.Select(t => new NeverVerifiesImplementationTask(t)).ToList();
    }

    return tasks;
  }

  public IObservable<AssertionBatchResult> BatchCompletions => verifier.BatchCompletions;

  class NeverVerifiesImplementationTask : IImplementationTask {
    private readonly IImplementationTask original;
    private readonly Subject<IVerificationStatus> source;

    public NeverVerifiesImplementationTask(IImplementationTask original) {
      this.original = original;
      source = new();
    }

    public IVerificationStatus CacheStatus => new Stale();
    public ProcessedProgram ProcessedProgram => original.ProcessedProgram;
    public Implementation Implementation => original.Implementation;

    public IObservable<IVerificationStatus> TryRun() {
      return source;
    }

    public bool IsIdle => false;

    public void Cancel() {
      source.OnError(new TaskCanceledException());
    }
  }

  public void Dispose() {
    verifier?.Dispose();
  }
}
